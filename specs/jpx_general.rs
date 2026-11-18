//! Actual general-layer source, component and definition composition.

use super::*;

verus! {

pub struct Part2GeneralLayerConfig {
    pub color: crate::jp2::ColorMethod,
    pub horizontal_grid: u16,
    pub vertical_grid: u16,
    pub registrations: Seq<crate::jp2::CodestreamRegistration>,
    pub definitions: Seq<(u16, (crate::ChannelType, crate::ChannelAssociation))>,
    pub opacity: Option<Part2SourceOpacity>,
}

pub type Part2GeneralSource = (Part1DecodedTypedImage, u8, u8, u32, u32);
pub type Part2GeneralSources = (Seq<Part2GeneralSource>, u32, u32);
pub type Part2GeneralComponents = (Seq<Part2TypedComponentOutput>, Seq<(u8, bool)>);

pub open spec fn part2_general_color_count(color: crate::jp2::ColorMethod) -> Result<usize, crate::DecodeError> {
    match color {
        crate::jp2::ColorMethod::Unspecified =>
            Err(crate::DecodeError::UnsupportedColorConversion { reason: crate::UnsupportedColorConversion::UnspecifiedColorSpace }),
        crate::jp2::ColorMethod::Enumerated { color_space: crate::jp2::ENUMERATED_GRAYSCALE } => Ok(1),
        crate::jp2::ColorMethod::Enumerated { color_space: crate::jp2::ENUMERATED_SRGB | crate::jp2::ENUMERATED_SYCC } => Ok(3),
        crate::jp2::ColorMethod::RestrictedIcc { .. } | crate::jp2::ColorMethod::AnyIcc { .. } =>
            Err(crate::DecodeError::UnsupportedColorConversion { reason: crate::UnsupportedColorConversion::IccProfile }),
        _ => Err(crate::DecodeError::UnsupportedColorConversion { reason: crate::UnsupportedColorConversion::EnumeratedColorSpace }),
    }
}

pub open spec fn part2_general_clear_definitions(
    input: Seq<Part2TypedComponentOutput>, count: nat,
) -> Seq<Part2TypedComponentOutput> {
    Seq::new(input.len(), |i: int| (input[i].0, if i < count { Seq::empty() } else { input[i].1 }))
}

pub open spec fn part2_general_validate_definition(
    definition: (crate::ChannelType, crate::ChannelAssociation), colors: usize,
) -> Result<(), crate::DecodeError> {
    match definition.1 {
        crate::ChannelAssociation::Color(value) if value == 0 || value as usize > colors => Err(part2_composition_error(false)),
        crate::ChannelAssociation::Unassociated if definition.0 == crate::ChannelType::Color => Err(part2_composition_error(false)),
        _ => Ok(()),
    }
}

pub open spec fn part2_general_source_count(config: Part2GeneralLayerConfig) -> nat {
    if config.registrations.len() == 0 { 1 } else { config.registrations.len() }
}

pub open spec fn part2_general_source_selection(
    config: Part2GeneralLayerConfig, layer_index: usize, index: nat,
) -> (usize, u8, u8, u32, u32) {
    if config.registrations.len() == 0 { (layer_index, 1, 1, 0, 0) }
    else {
        let value = config.registrations[index as int];
        (value.codestream_index as usize, value.horizontal_subsampling, value.vertical_subsampling,
            value.horizontal_offset, value.vertical_offset)
    }
}

#[verifier::opaque]
pub open spec fn part2_general_source_step(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, index: nat, previous: Part2GeneralSources,
) -> Result<Part2GeneralSources, crate::DecodeError> {
    let selected = part2_general_source_selection(config, layer_index, index);
    match part2_decode_jpx_codestream(file, selected.0, limits) {
        Err(error) => Err(error),
        Ok(decoded) => part2_general_source_finish(config, selected, previous, decoded),
    }
}

pub open spec fn part2_general_source_finish(
    config: Part2GeneralLayerConfig, selected: (usize, u8, u8, u32, u32), previous: Part2GeneralSources,
    decoded: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>),
) -> Result<Part2GeneralSources, crate::DecodeError> {
    match part2_native_registered_extent(decoded.0.0.0, selected.1 as u32, config.horizontal_grid as u32, selected.3) {
            Err(error) => Err(error),
            Ok(width) => match part2_native_registered_extent(decoded.0.0.1, selected.2 as u32, config.vertical_grid as u32, selected.4) {
                Err(error) => Err(error),
                Ok(height) => Ok((previous.0.push((decoded.0, selected.1, selected.2, selected.3, selected.4)),
                    if previous.1 < width { previous.1 } else { width },
                    if previous.2 < height { previous.2 } else { height })),
            },
    }
}

pub(crate) open spec fn part2_general_source_cold_step(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, index: nat, previous: Part2GeneralSources, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2GeneralSources> {
    let selected = part2_general_source_selection(config, layer_index, index);
    part2_jpip_snapshot_bind(part2_jpx_cold_run(file, selected.0, limits, events),
        |decoded, tail| Some((part2_general_source_finish(config, selected, previous, decoded), tail)))
}

#[verifier::opaque]
pub(crate) open spec fn part2_general_sources_cold_prefix(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, count: nat, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2GeneralSources>
    decreases count,
{
    if count == 0 { Some((Ok((Seq::empty(), u32::MAX, u32::MAX)), events)) }
    else {
        part2_jpip_snapshot_bind(part2_general_sources_cold_prefix(file, config, layer_index, limits,
            (count - 1) as nat, events), |previous, tail|
                part2_general_source_cold_step(file, config, layer_index, limits, (count - 1) as nat, previous, tail))
    }
}

pub(crate) open spec fn part2_general_after_cold_sources(
    config: Part2GeneralLayerConfig, colors: usize, sources: Part2GeneralSources, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    let width = sources.1;
    let height = sources.2;
    if width == 0 || height == 0 || width == u32::MAX || height == u32::MAX {
        Err(part2_composition_error(false))
    } else if width as nat * height as nat > crate::limits::resource_pixel_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Pixels,
            limit: crate::limits::resource_pixel_limit(limits), actual: (width as nat * height as nat) as u64 })
    } else {
        part2_general_after_assembly(config, colors, width, height,
            part2_general_assembled_sources_prefix(sources.0, config, width, height, sources.0.len()), limits)
    }
}

pub(crate) open spec fn part2_general_color_context(config:Part2GeneralLayerConfig,colors:usize,sources:Part2GeneralSources,
    limits:&crate::ResourceLimits)->Option<Part2ColorConvertContext> {
    let width=sources.1;let height=sources.2;
    if width==0 || height==0 || width==u32::MAX || height==u32::MAX
        || width as nat*height as nat>crate::limits::resource_pixel_limit(limits) {None}else{
        match part2_general_assembled_sources_prefix(sources.0,config,width,height,sources.0.len()) {
            Err(_)=>None,Ok(components)=>if components.0.len()>crate::limits::resource_component_limit(limits){None}else{
                match part2_general_definitions(config,colors,components.0) {
                    Err(_)=>None,Ok(defined)=>match part2_typed_image_from_parts(width,height,0,0,defined,
                        crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits)) {
                        Err(_)=>None,Ok(image)=>Some(Part2ColorConvertContext {image,method:config.color,
                            bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)}),
                    },
                }
            },
        }
    }
}
pub(crate) open spec fn part2_general_finish_color_requests(config:Part2GeneralLayerConfig,colors:usize,sources:Part2GeneralSources,
    limits:&crate::ResourceLimits)->Seq<Part2ColorOutputCapacity> {
    match part2_general_color_context(config,colors,sources,limits){None=>Seq::empty(),Some(context)=>part2_color_convert_requests(context)}
}
pub(crate) open spec fn part2_general_normalize_context(source:Part2GeneralSource,index:nat)->Part2ColorNormalizeContext {
    Part2ColorNormalizeContext {component:source.0.1[index as int],width:source.0.0.0,height:source.0.0.1,x:source.0.0.2,y:source.0.0.3}
}
pub(crate) open spec fn part2_general_component_copy_context(source:Part2GeneralSource,config:Part2GeneralLayerConfig,
    width:u32,height:u32,component:nat,initial:Part2GeneralComponents)->Option<Part2TypedCapacityContext> {
    if component>=source.0.1.len(){None}else{
        match part2_general_components_prefix(source,config,width,height,component,initial) {
            Err(_)=>None,Ok(before)=>match part2_general_component_step(source,config,width,height,component,before) {
                Err(_)=>None,Ok(after)=>Some(Part2TypedCapacityContext::DefinitionCopy {
                    source:(source.0.1[component as int],source.0.2[component as int]),
                    target:(after.0[before.0.len() as int].0,Seq::empty()),
                }),
            },
        }
    }
}
pub(crate) open spec fn part2_general_component_copy_requests(source:Part2GeneralSource,config:Part2GeneralLayerConfig,
    width:u32,height:u32,component:nat,initial:Part2GeneralComponents)->Seq<Part2ColorOutputCapacity> {
    match part2_general_component_copy_context(source,config,width,height,component,initial) {
        None=>Seq::empty(),Some(context)=>seq![Part2ColorOutputCapacity::Definition {context}],
    }
}
pub(crate) open spec fn part2_general_component_storage_requests(source:Part2GeneralSource,config:Part2GeneralLayerConfig,
    width:u32,height:u32,component:nat,initial:Part2GeneralComponents)->Seq<Part2ColorOutputCapacity> {
    if component>=source.0.1.len() || part2_general_components_prefix(source,config,width,height,component,initial).is_err(){Seq::empty()}else{
        part2_color_normalize_requests(part2_general_normalize_context(source,component))
            +part2_general_component_copy_requests(source,config,width,height,component,initial)
    }
}
pub(crate) open spec fn part2_general_normalize_source_requests(config:Part2GeneralLayerConfig,sources:Part2GeneralSources,index:nat)->Seq<Part2ColorOutputCapacity> {
    if index>=sources.0.len(){Seq::empty()}else{
        match part2_general_assembled_sources_prefix(sources.0,config,sources.1,sources.2,index) {
            Err(_)=>Seq::empty(),Ok(initial)=>part2_color_output_trace(|component:nat|
                part2_general_component_storage_requests(sources.0[index as int],config,sources.1,sources.2,component,initial),
                sources.0[index as int].0.1.len()),
        }
    }
}
pub(crate) open spec fn part2_general_normalize_requests(config:Part2GeneralLayerConfig,sources:Part2GeneralSources,limits:&crate::ResourceLimits)->Seq<Part2ColorOutputCapacity> {
    if sources.1==0 || sources.2==0 || sources.1==u32::MAX || sources.2==u32::MAX
        || sources.1 as nat*sources.2 as nat>crate::limits::resource_pixel_limit(limits) {Seq::empty()}else{
        part2_color_output_trace(|index|part2_general_normalize_source_requests(config,sources,index),sources.0.len())
    }
}
pub(crate) open spec fn part2_general_color_requests(config:Part2GeneralLayerConfig,colors:usize,sources:Part2GeneralSources,
    limits:&crate::ResourceLimits)->Seq<Part2ColorOutputCapacity> {
    part2_general_normalize_requests(config,sources,limits)+part2_general_finish_storage_requests(config,colors,sources,limits)
}
pub(crate) open spec fn part2_general_definition_input(config:Part2GeneralLayerConfig,sources:Part2GeneralSources,limits:&crate::ResourceLimits)
    ->Option<Seq<Part2TypedComponentOutput>> {
    if sources.1==0 || sources.2==0 || sources.1==u32::MAX || sources.2==u32::MAX
        || sources.1 as nat*sources.2 as nat>crate::limits::resource_pixel_limit(limits) {None}else{
        match part2_general_assembled_sources_prefix(sources.0,config,sources.1,sources.2,sources.0.len()) {
            Err(_)=>None,Ok(components)=>if components.0.len()>crate::limits::resource_component_limit(limits){None}else{Some(components.0)},
        }
    }
}
pub(crate) open spec fn part2_general_record_definition_context(config:Part2GeneralLayerConfig,colors:usize,
    input:Seq<Part2TypedComponentOutput>,index:nat)->Option<Part2TypedCapacityContext> {
    if index>=config.definitions.len(){None}else{
        let record=config.definitions[index as int];
        match part2_general_records_prefix(config.definitions,colors,part2_general_clear_definitions(input,input.len()),index) {
            Err(_)=>None,Ok(before)=>if part2_general_validate_definition(record.1,colors).is_err() || record.0>=before.len(){None}else{
                Some(Part2TypedCapacityContext::Definition {source:before[record.0 as int],definition:record.1})
            },
        }
    }
}
pub(crate) open spec fn part2_general_record_definition_requests(config:Part2GeneralLayerConfig,colors:usize,
    input:Seq<Part2TypedComponentOutput>,index:nat)->Seq<Part2ColorOutputCapacity> {
    match part2_general_record_definition_context(config,colors,input,index) {
        None=>Seq::empty(),Some(context)=>seq![Part2ColorOutputCapacity::Definition {context}],
    }
}
pub(crate) open spec fn part2_general_default_definition_context(input:Seq<Part2TypedComponentOutput>,index:nat)
    ->Part2TypedCapacityContext {
    Part2TypedCapacityContext::Definition {
        source:part2_general_default_colors(part2_general_clear_definitions(input,input.len()),index)[index as int],
        definition:(crate::ChannelType::Color,crate::ChannelAssociation::Color((index+1) as u16)),
    }
}
pub(crate) open spec fn part2_general_opacity_definition_context(input:Seq<Part2TypedComponentOutput>,colors:usize,opacity:Part2SourceOpacity)
    ->Part2TypedCapacityContext {
    Part2TypedCapacityContext::Definition {
        source:part2_general_default_colors(part2_general_clear_definitions(input,input.len()),colors as nat)[colors as int],
        definition:(if opacity==Part2SourceOpacity::Premultiplied {crate::ChannelType::PremultipliedOpacity}else{crate::ChannelType::Opacity},
            crate::ChannelAssociation::WholeImage),
    }
}
pub(crate) open spec fn part2_general_default_definition_requests(input:Seq<Part2TypedComponentOutput>,colors:usize,opacity:Part2SourceOpacity)
    ->Seq<Part2ColorOutputCapacity> {
    if input.len()<colors {Seq::empty()}else{
        part2_color_output_trace(|index:nat|if index>=u16::MAX{Seq::empty()}else{
            seq![Part2ColorOutputCapacity::Definition {context:part2_general_default_definition_context(input,index)}]
        },colors as nat)
        +if matches!(opacity,Part2SourceOpacity::ChromaKey {..}) || colors>u16::MAX
            || colors as nat+1>usize::MAX || input.len()!=colors as nat+1 {Seq::empty()}else{
            seq![Part2ColorOutputCapacity::Definition {context:part2_general_opacity_definition_context(input,colors,opacity)}]
        }
    }
}
pub(crate) open spec fn part2_general_finish_definition_requests(config:Part2GeneralLayerConfig,colors:usize,sources:Part2GeneralSources,
    limits:&crate::ResourceLimits)->Seq<Part2ColorOutputCapacity> {
    match part2_general_definition_input(config,sources,limits) {
        None=>Seq::empty(),Some(input)=>if config.definitions.len()>0 {
            part2_color_output_trace(|index|part2_general_record_definition_requests(config,colors,input,index),config.definitions.len())
        }else{match config.opacity {None=>Seq::empty(),Some(opacity)=>part2_general_default_definition_requests(input,colors,opacity)}},
    }
}
pub(crate) open spec fn part2_general_finish_storage_requests(config:Part2GeneralLayerConfig,colors:usize,sources:Part2GeneralSources,
    limits:&crate::ResourceLimits)->Seq<Part2ColorOutputCapacity> {
    part2_general_finish_definition_requests(config,colors,sources,limits)+part2_general_finish_color_requests(config,colors,sources,limits)
}
pub(crate) open spec fn part2_general_after_cold_sources_run(config:Part2GeneralLayerConfig,colors:usize,sources:Part2GeneralSources,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2OwnedLayer> {
    part2_color_output_program_run(part2_general_color_requests(config,colors,sources,limits),part2_general_after_cold_sources(config,colors,sources,limits),events)
}
pub(crate) proof fn part2_general_after_cold_sources_normal(config:Part2GeneralLayerConfig,colors:usize,sources:Part2GeneralSources,limits:&crate::ResourceLimits)
    ensures part2_cold_framed(|events|part2_general_after_cold_sources_run(config,colors,sources,limits,events),part2_general_after_cold_sources(config,colors,sources,limits)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2OwnedLayer>|
            (forall|events|#[trigger]other(events)==part2_general_after_cold_sources_run(config,colors,sources,limits,events))
                ==>#[trigger]part2_cold_framed(other,part2_general_after_cold_sources(config,colors,sources,limits)),
{
    let requests=part2_general_color_requests(config,colors,sources,limits);
    let value=part2_general_after_cold_sources(config,colors,sources,limits);
    part2_color_output_program_normal(requests,value);
    part2_decode_eta(|events|part2_color_output_program_run(requests,value,events),value);
    part2_decode_eta(|events|part2_general_after_cold_sources_run(config,colors,sources,limits,events),value);
}
pub(crate) open spec fn part2_general_layer_cold_run(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2OwnedLayer> {
    match part2_general_color_count(config.color) {
        Err(error) => Some((Err(error), events)),
        Ok(colors) => part2_jpip_snapshot_bind(
            part2_general_sources_cold_prefix(file, config, layer_index, limits, part2_general_source_count(config), events),
            |sources, tail| part2_general_after_cold_sources_run(config, colors, sources, limits,tail)),
    }
}

pub(crate) open spec fn part2_general_layer_cold_result(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, result: Part2OwnedLayerResult,
) -> bool {
    part2_cold_framed(|events| part2_general_layer_cold_run(file, config, layer_index, limits, events), result)
}

pub(crate) proof fn part2_general_source_cold_normal(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, index: nat, previous: Part2GeneralSources,
)
    ensures part2_cold_framed(
        |events| part2_general_source_cold_step(file, config, layer_index, limits, index, previous, events),
        part2_general_source_step(file, config, layer_index, limits, index, previous)),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2GeneralSources>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_general_source_cold_step(file, config, layer_index, limits, index, previous, events))
                ==> #[trigger] part2_cold_framed(run,
                    part2_general_source_step(file, config, layer_index, limits, index, previous)),
{
    reveal(part2_general_source_step);
    let selected = part2_general_source_selection(config, layer_index, index);
    let decoded = part2_decode_jpx_codestream(file, selected.0, limits);
    part2_jpx_cold_normal(file, selected.0, limits);
    if let Ok(value) = decoded { part2_cold_pure(part2_general_source_finish(config, selected, previous, value)); }
    part2_cold_bind(
        |events| part2_jpx_cold_run(file, selected.0, limits, events),
        |value, tail| Some((part2_general_source_finish(config, selected, previous, value), tail)),
        decoded, part2_general_source_step(file, config, layer_index, limits, index, previous));
}

pub(crate) proof fn part2_general_sources_cold_normal(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, count: nat,
)
    ensures part2_cold_framed(
        |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, count, events),
        part2_general_sources_prefix(file, config, layer_index, limits, count)),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2GeneralSources>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_general_sources_cold_prefix(file, config, layer_index, limits, count, events))
                ==> #[trigger] part2_cold_framed(run,
                    part2_general_sources_prefix(file, config, layer_index, limits, count)),
    decreases count,
{
    reveal_with_fuel(part2_general_sources_cold_prefix, 1);
    reveal_with_fuel(part2_general_sources_prefix, 1);
    if count == 0 { part2_cold_pure(Ok((Seq::<Part2GeneralSource>::empty(), u32::MAX, u32::MAX))); }
    else {
        let prior = part2_general_sources_prefix(file, config, layer_index, limits, (count - 1) as nat);
        part2_general_sources_cold_normal(file, config, layer_index, limits, (count - 1) as nat);
        if let Ok(previous) = prior {
            part2_general_source_cold_normal(file, config, layer_index, limits, (count - 1) as nat, previous);
        }
        part2_cold_bind(
            |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, (count - 1) as nat, events),
            |previous, tail| part2_general_source_cold_step(file, config, layer_index, limits, (count - 1) as nat, previous, tail),
            prior, part2_general_sources_prefix(file, config, layer_index, limits, count));
    }
}

pub(crate) proof fn part2_general_layer_cold_normal(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize, limits: &crate::ResourceLimits,
)
    ensures part2_general_layer_cold_result(file, config, layer_index, limits,
        part2_decode_general_layer(file, config, layer_index, limits)),
{
    reveal(part2_decode_general_layer);
    match part2_general_color_count(config.color) {
        Err(error) => { part2_cold_pure::<Part2OwnedLayer>(Err(error)); },
        Ok(colors) => {
            let sources = part2_general_sources_prefix(file, config, layer_index, limits, part2_general_source_count(config));
            part2_general_sources_cold_normal(file, config, layer_index, limits, part2_general_source_count(config));
            if let Ok(value) = sources { part2_general_after_cold_sources_normal(config, colors, value, limits); }
            part2_cold_bind(
                |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, part2_general_source_count(config), events),
                |value, tail| part2_general_after_cold_sources_run(config, colors, value, limits,tail),
                sources, part2_decode_general_layer(file, config, layer_index, limits));
        },
    }
}

pub(crate) proof fn part2_general_color_error(file:Part2JpxDecodeInput,config:Part2GeneralLayerConfig,layer_index:usize,
    colors:usize,sources:Part2GeneralSources,limits:&crate::ResourceLimits,context:Part2ColorConvertContext,error:crate::DecodeError)
    requires part2_general_color_count(config.color)==Ok(colors),
        part2_general_sources_prefix(file,config,layer_index,limits,part2_general_source_count(config))==Ok(sources),
        part2_general_color_context(config,colors,sources,limits)==Some(context),
        part2_color_convert_storage_result(context,Err(error)),
        part2_color_convert_value(context)==Err(error) ==> part2_general_after_cold_sources(config,colors,sources,limits)==Err(error),
    ensures part2_general_layer_cold_result(file,config,layer_index,limits,Err(error)),
{
    part2_color_convert_storage_frames(context,Err(error));
    let requests=part2_color_convert_requests(context);
    let ordinary=part2_general_after_cold_sources(config,colors,sources,limits);
    part2_decode_eta(|events|part2_color_output_program_run(requests,part2_color_convert_value(context),events),Err(error));
    let whole=part2_general_color_requests(config,colors,sources,limits);
    assert forall|request:Part2ColorOutputCapacity|requests.contains(request) implies whole.contains(request) by {
        part2_color_output_concat_member(part2_general_finish_definition_requests(config,colors,sources,limits),requests,request);
        part2_color_output_concat_member(part2_general_normalize_requests(config,sources,limits),
            part2_general_finish_storage_requests(config,colors,sources,limits),request);
    }
    part2_color_output_program_child_error(whole,ordinary,requests,part2_color_convert_value(context),error);
    part2_decode_eta(|events|part2_color_output_program_run(whole,ordinary,events),Err(error));
    part2_general_sources_cold_normal(file,config,layer_index,limits,part2_general_source_count(config));
    part2_cold_bind(|events|part2_general_sources_cold_prefix(file,config,layer_index,limits,part2_general_source_count(config),events),
        |sources,tail|part2_general_after_cold_sources_run(config,colors,sources,limits,tail),Ok(sources),Err(error));
}
pub(crate) proof fn part2_general_normalize_error(file:Part2JpxDecodeInput,config:Part2GeneralLayerConfig,layer_index:usize,
    colors:usize,sources:Part2GeneralSources,limits:&crate::ResourceLimits,source_index:nat,component:nat,initial:Part2GeneralComponents,error:crate::DecodeError)
    requires part2_general_color_count(config.color)==Ok(colors),
        part2_general_sources_prefix(file,config,layer_index,limits,part2_general_source_count(config))==Ok(sources),
        sources.1>0,sources.2>0,sources.1<u32::MAX,sources.2<u32::MAX,
        sources.1 as nat*sources.2 as nat<=crate::limits::resource_pixel_limit(limits),
        source_index<sources.0.len(),component<sources.0[source_index as int].0.1.len(),
        part2_general_assembled_sources_prefix(sources.0,config,sources.1,sources.2,source_index)==Ok(initial),
        part2_general_components_prefix(sources.0[source_index as int],config,sources.1,sources.2,component,initial).is_ok(),
        part2_color_normalize_storage_result(part2_general_normalize_context(sources.0[source_index as int],component),Err(error)),
        part2_color_normalize_value(part2_general_normalize_context(sources.0[source_index as int],component))==Err(error)
            ==>part2_general_after_cold_sources(config,colors,sources,limits)==Err(error),
    ensures part2_general_layer_cold_result(file,config,layer_index,limits,Err(error)),
{
    let context=part2_general_normalize_context(sources.0[source_index as int],component);
    let request=Part2ColorOutputCapacity::Normalize {context};
    let component_step=|i:nat|part2_general_component_storage_requests(
        sources.0[source_index as int],config,sources.1,sources.2,i,initial);
    assert(part2_color_normalize_requests(context)[0]==request);
    assert(part2_color_normalize_requests(context).contains(request));
    part2_color_output_concat_member(part2_color_normalize_requests(context),
        part2_general_component_copy_requests(sources.0[source_index as int],config,sources.1,sources.2,component,initial),request);
    part2_color_output_trace_member(component_step,sources.0[source_index as int].0.1.len(),component,request);
    let source_step=|i|part2_general_normalize_source_requests(config,sources,i);
    part2_color_output_trace_member(source_step,sources.0.len(),source_index,request);
    part2_color_output_concat_member(part2_general_normalize_requests(config,sources,limits),
        part2_general_finish_storage_requests(config,colors,sources,limits),request);
    let whole=part2_general_color_requests(config,colors,sources,limits);
    assert forall|child:Part2ColorOutputCapacity|part2_color_normalize_requests(context).contains(child) implies whole.contains(child) by {
        assert(child==request);
    }
    let ordinary=part2_general_after_cold_sources(config,colors,sources,limits);
    part2_color_output_program_child_error(whole,ordinary,part2_color_normalize_requests(context),part2_color_normalize_value(context),error);
    part2_decode_eta(|events|part2_color_output_program_run(whole,ordinary,events),Err(error));
    part2_general_sources_cold_normal(file,config,layer_index,limits,part2_general_source_count(config));
    part2_cold_bind(|events|part2_general_sources_cold_prefix(file,config,layer_index,limits,part2_general_source_count(config),events),
        |sources,tail|part2_general_after_cold_sources_run(config,colors,sources,limits,tail),Ok(sources),Err(error));
}
pub(crate) proof fn part2_general_finish_definition_member(config:Part2GeneralLayerConfig,colors:usize,
    sources:Part2GeneralSources,limits:&crate::ResourceLimits,request:Part2ColorOutputCapacity)
    requires part2_general_finish_definition_requests(config,colors,sources,limits).contains(request),
    ensures part2_general_color_requests(config,colors,sources,limits).contains(request),
{
    part2_color_output_concat_member(part2_general_finish_definition_requests(config,colors,sources,limits),
        part2_general_finish_color_requests(config,colors,sources,limits),request);
    part2_color_output_concat_member(part2_general_normalize_requests(config,sources,limits),
        part2_general_finish_storage_requests(config,colors,sources,limits),request);
}
pub(crate) proof fn part2_general_component_definition_member(config:Part2GeneralLayerConfig,colors:usize,
    sources:Part2GeneralSources,limits:&crate::ResourceLimits,source_index:nat,component:nat,initial:Part2GeneralComponents,
    context:Part2TypedCapacityContext)
    requires sources.1>0,sources.2>0,sources.1<u32::MAX,sources.2<u32::MAX,
        sources.1 as nat*sources.2 as nat<=crate::limits::resource_pixel_limit(limits),
        source_index<sources.0.len(),component<sources.0[source_index as int].0.1.len(),
        part2_general_assembled_sources_prefix(sources.0,config,sources.1,sources.2,source_index)==Ok(initial),
        part2_general_component_copy_context(sources.0[source_index as int],config,sources.1,sources.2,component,initial)==Some(context),
    ensures part2_general_color_requests(config,colors,sources,limits).contains(Part2ColorOutputCapacity::Definition {context}),
{
    let source=sources.0[source_index as int];
    let request=Part2ColorOutputCapacity::Definition {context};
    let copy=part2_general_component_copy_requests(source,config,sources.1,sources.2,component,initial);
    assert(copy[0]==request);assert(copy.contains(request));
    part2_color_output_concat_member(part2_color_normalize_requests(part2_general_normalize_context(source,component)),copy,request);
    let components_step=|i:nat|part2_general_component_storage_requests(source,config,sources.1,sources.2,i,initial);
    part2_color_output_trace_member(components_step,source.0.1.len(),component,request);
    let source_step=|i|part2_general_normalize_source_requests(config,sources,i);
    part2_color_output_trace_member(source_step,sources.0.len(),source_index,request);
    part2_color_output_concat_member(part2_general_normalize_requests(config,sources,limits),
        part2_general_finish_storage_requests(config,colors,sources,limits),request);
}
pub(crate) proof fn part2_general_record_definition_member(config:Part2GeneralLayerConfig,colors:usize,
    sources:Part2GeneralSources,limits:&crate::ResourceLimits,input:Seq<Part2TypedComponentOutput>,
    index:nat,context:Part2TypedCapacityContext)
    requires part2_general_definition_input(config,sources,limits)==Some(input),config.definitions.len()>0,
        part2_general_record_definition_context(config,colors,input,index)==Some(context),
    ensures part2_general_color_requests(config,colors,sources,limits).contains(Part2ColorOutputCapacity::Definition {context}),
{
    let request=Part2ColorOutputCapacity::Definition {context};
    let step=|i|part2_general_record_definition_requests(config,colors,input,i);
    assert(step(index)[0]==request);assert(step(index).contains(request));
    part2_color_output_trace_member(step,config.definitions.len(),index,request);
    part2_general_finish_definition_member(config,colors,sources,limits,request);
}
pub(crate) proof fn part2_general_default_definition_member(config:Part2GeneralLayerConfig,colors:usize,
    sources:Part2GeneralSources,limits:&crate::ResourceLimits,input:Seq<Part2TypedComponentOutput>,opacity:Part2SourceOpacity,index:nat)
    requires part2_general_definition_input(config,sources,limits)==Some(input),config.definitions.len()==0,
        config.opacity==Some(opacity),input.len()>=colors,index<colors,index<u16::MAX,
    ensures part2_general_color_requests(config,colors,sources,limits).contains(
        Part2ColorOutputCapacity::Definition {context:part2_general_default_definition_context(input,index)}),
{
    let request=Part2ColorOutputCapacity::Definition {context:part2_general_default_definition_context(input,index)};
    let step=|i:nat|if i>=u16::MAX{Seq::empty()}else{
        seq![Part2ColorOutputCapacity::Definition {context:part2_general_default_definition_context(input,i)}]
    };
    assert(step(index)[0]==request);assert(step(index).contains(request));
    part2_color_output_trace_member(step,colors as nat,index,request);
    let opacity_request=if matches!(opacity,Part2SourceOpacity::ChromaKey {..}) || colors>u16::MAX
        || colors as nat+1>usize::MAX || input.len()!=colors as nat+1 {Seq::empty()}else{
        seq![Part2ColorOutputCapacity::Definition {context:part2_general_opacity_definition_context(input,colors,opacity)}]
    };
    part2_color_output_concat_member(part2_color_output_trace(step,colors as nat),opacity_request,request);
    part2_general_finish_definition_member(config,colors,sources,limits,request);
}
pub(crate) proof fn part2_general_opacity_definition_member(config:Part2GeneralLayerConfig,colors:usize,
    sources:Part2GeneralSources,limits:&crate::ResourceLimits,input:Seq<Part2TypedComponentOutput>,opacity:Part2SourceOpacity)
    requires part2_general_definition_input(config,sources,limits)==Some(input),config.definitions.len()==0,
        config.opacity==Some(opacity),!matches!(opacity,Part2SourceOpacity::ChromaKey {..}),colors<=u16::MAX,
        colors as nat+1<=usize::MAX,input.len()==colors as nat+1,
    ensures part2_general_color_requests(config,colors,sources,limits).contains(
        Part2ColorOutputCapacity::Definition {context:part2_general_opacity_definition_context(input,colors,opacity)}),
{
    let request=Part2ColorOutputCapacity::Definition {context:part2_general_opacity_definition_context(input,colors,opacity)};
    let opacity_request=seq![request];assert(opacity_request[0]==request);assert(opacity_request.contains(request));
    let step=|i:nat|if i>=u16::MAX{Seq::empty()}else{
        seq![Part2ColorOutputCapacity::Definition {context:part2_general_default_definition_context(input,i)}]
    };
    part2_color_output_concat_member(part2_color_output_trace(step,colors as nat),opacity_request,request);
    part2_general_finish_definition_member(config,colors,sources,limits,request);
}
pub(crate) proof fn part2_general_definition_error(file:Part2JpxDecodeInput,config:Part2GeneralLayerConfig,layer_index:usize,
    colors:usize,sources:Part2GeneralSources,limits:&crate::ResourceLimits,context:Part2TypedCapacityContext,error:crate::DecodeError)
    requires part2_general_color_count(config.color)==Ok(colors),
        part2_general_sources_prefix(file,config,layer_index,limits,part2_general_source_count(config))==Ok(sources),
        part2_general_color_requests(config,colors,sources,limits).contains(Part2ColorOutputCapacity::Definition {context}),
        matches!(context,Part2TypedCapacityContext::Definition {..}|Part2TypedCapacityContext::DefinitionCopy {..}),
        part2_definition_storage_result(context,Err(error)),
    ensures part2_general_layer_cold_result(file,config,layer_index,limits,Err(error)),
{
    part2_color_definition_storage_observed(context,Err(error));
    let whole=part2_general_color_requests(config,colors,sources,limits);
    let ordinary=part2_general_after_cold_sources(config,colors,sources,limits);
    part2_color_output_program_refused(whole,ordinary,Part2ColorOutputCapacity::Definition {context},error);
    part2_decode_eta(|events|part2_color_output_program_run(whole,ordinary,events),Err(error));
    part2_general_sources_cold_normal(file,config,layer_index,limits,part2_general_source_count(config));
    part2_cold_bind(|events|part2_general_sources_cold_prefix(file,config,layer_index,limits,part2_general_source_count(config),events),
        |sources,tail|part2_general_after_cold_sources_run(config,colors,sources,limits,tail),Ok(sources),Err(error));
}
pub(crate) proof fn part2_general_cold_error_extend(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize, limits: &crate::ResourceLimits,
    count: nat, total: nat, error: crate::DecodeError,
)
    requires count <= total, part2_cold_framed(
        |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, count, events), Err(error)),
    ensures part2_cold_framed(
        |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, total, events), Err(error)),
    decreases total - count,
{
    if count < total {
        part2_general_cold_error_extend(file, config, layer_index, limits, count, (total - 1) as nat, error);
        reveal_with_fuel(part2_general_sources_cold_prefix, 1);
        part2_cold_bind(
            |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, (total - 1) as nat, events),
            |previous, tail| part2_general_source_cold_step(file, config, layer_index, limits, (total - 1) as nat, previous, tail),
            Err(error), Err(error));
    }
}

pub(crate) proof fn part2_general_layer_cold_source_error(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize, limits: &crate::ResourceLimits,
    index: nat, previous: Part2GeneralSources, colors: usize, error: crate::DecodeError,
)
    requires part2_general_color_count(config.color) == Ok(colors), index < part2_general_source_count(config),
        part2_general_sources_prefix(file, config, layer_index, limits, index) == Ok(previous),
        part2_jpx_cold_result(file, part2_general_source_selection(config, layer_index, index).0, limits, Err(error)),
    ensures part2_general_layer_cold_result(file, config, layer_index, limits, Err(error)),
{
    let selected = part2_general_source_selection(config, layer_index, index);
    part2_general_sources_cold_normal(file, config, layer_index, limits, index);
    part2_cold_bind(
        |events| part2_jpx_cold_run(file, selected.0, limits, events),
        |decoded, tail| Some((part2_general_source_finish(config, selected, previous, decoded), tail)),
        Err(error), Err(error));
    reveal_with_fuel(part2_general_sources_cold_prefix, 1);
    part2_cold_bind(
        |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, index, events),
        |previous, tail| part2_general_source_cold_step(file, config, layer_index, limits, index, previous, tail),
        Ok(previous), Err(error));
    part2_general_cold_error_extend(file, config, layer_index, limits, index + 1, part2_general_source_count(config), error);
    part2_cold_bind(
        |events| part2_general_sources_cold_prefix(file, config, layer_index, limits, part2_general_source_count(config), events),
        |sources, tail| part2_general_after_cold_sources_run(config, colors, sources, limits,tail),
        Err(error), Err(error));
}

#[verifier::opaque]
pub open spec fn part2_general_sources_prefix(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, count: nat,
) -> Result<Part2GeneralSources, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), u32::MAX, u32::MAX)) }
    else {
        match part2_general_sources_prefix(file, config, layer_index, limits, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_general_source_step(file, config, layer_index, limits, (count - 1) as nat, previous),
        }
    }
}

pub(crate) proof fn part2_general_sources_step(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, count: nat,
)
    ensures part2_general_sources_prefix(file, config, layer_index, limits, count + 1)
        == match part2_general_sources_prefix(file, config, layer_index, limits, count) {
            Err(error) => Err(error),
            Ok(previous) => part2_general_source_step(file, config, layer_index, limits, count, previous),
        },
{
    reveal(part2_general_sources_prefix);
}

#[verifier::opaque]
pub open spec fn part2_general_component_step(
    source: Part2GeneralSource, config: Part2GeneralLayerConfig, width: u32, height: u32,
    index: nat, previous: Part2GeneralComponents,
) -> Result<Part2GeneralComponents, crate::DecodeError> {
    let image = source.0;
    let component = image.1[index as int];
    match color_normalize_component(component, image.0.0, image.0.1, image.0.2, image.0.3) {
        Err(error) => Err(error),
        Ok(normalized) => match part2_register_component_plane(Part2PlaneRegistration {
            source: normalized, source_width: image.0.0, source_height: image.0.1,
            width, height, horizontal_subsampling: source.1 as u32, vertical_subsampling: source.2 as u32,
            horizontal_grid: config.horizontal_grid as u32, vertical_grid: config.vertical_grid as u32,
            horizontal_offset: source.3, vertical_offset: source.4,
        }) {
            Err(error) => Err(error),
            Ok(samples) => {
                let assembled = part2_typed_component_from_parts(width, height,
                    crate::codestream::ComponentInfo { precision: 16, signed: false,
                        x_subsampling: 1, y_subsampling: 1, x_registration: 0, y_registration: 0 },
                    Part1TypedSampleSequence::Unsigned(Seq::new(samples.len(), |i: int| samples[i] as u64)));
                Ok((previous.0.push((assembled.0, image.2[index as int])),
                    previous.1.push((component.info.precision, component.info.signed))))
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_general_components_prefix(
    source: Part2GeneralSource, config: Part2GeneralLayerConfig, width: u32, height: u32,
    count: nat, initial: Part2GeneralComponents,
) -> Result<Part2GeneralComponents, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) }
    else {
        match part2_general_components_prefix(source, config, width, height, (count - 1) as nat, initial) {
            Err(error) => Err(error),
            Ok(previous) => part2_general_component_step(source, config, width, height, (count - 1) as nat, previous),
        }
    }
}

pub(crate) proof fn part2_general_components_step(
    source: Part2GeneralSource, config: Part2GeneralLayerConfig, width: u32, height: u32,
    count: nat, initial: Part2GeneralComponents,
)
    ensures part2_general_components_prefix(source, config, width, height, count + 1, initial)
        == match part2_general_components_prefix(source, config, width, height, count, initial) {
            Err(error) => Err(error),
            Ok(previous) => part2_general_component_step(source, config, width, height, count, previous),
        },
{
    reveal(part2_general_components_prefix);
}

#[verifier::opaque]
pub open spec fn part2_general_assembled_sources_prefix(
    sources: Seq<Part2GeneralSource>, config: Part2GeneralLayerConfig, width: u32, height: u32, count: nat,
) -> Result<Part2GeneralComponents, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), Seq::empty())) }
    else {
        match part2_general_assembled_sources_prefix(sources, config, width, height, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                let source = sources[count - 1];
                part2_general_components_prefix(source, config, width, height, source.0.1.len(), previous)
            },
        }
    }
}

pub(crate) proof fn part2_general_assembled_sources_step(
    sources: Seq<Part2GeneralSource>, config: Part2GeneralLayerConfig, width: u32, height: u32, count: nat,
)
    ensures part2_general_assembled_sources_prefix(sources, config, width, height, count + 1)
        == match part2_general_assembled_sources_prefix(sources, config, width, height, count) {
            Err(error) => Err(error),
            Ok(previous) => part2_general_components_prefix(sources[count as int], config, width, height,
                sources[count as int].0.1.len(), previous),
        },
{
    reveal(part2_general_assembled_sources_prefix);
}

pub open spec fn part2_general_append_definition(
    components: Seq<Part2TypedComponentOutput>, index: nat, definition: ColorDefinition,
) -> Result<Seq<Part2TypedComponentOutput>, crate::DecodeError> {
    if index >= components.len() { Err(part2_composition_error(false)) }
    else { Ok(components.update(index as int, (components[index as int].0,
        components[index as int].1.push(definition)))) }
}

#[verifier::opaque]
pub open spec fn part2_general_records_prefix(
    records: Seq<(u16, ColorDefinition)>, colors: usize,
    initial: Seq<Part2TypedComponentOutput>, count: nat,
) -> Result<Seq<Part2TypedComponentOutput>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) }
    else {
        match part2_general_records_prefix(records, colors, initial, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                let record = records[count - 1];
                match part2_general_validate_definition(record.1, colors) {
                    Err(error) => Err(error),
                    Ok(()) => part2_general_append_definition(previous, record.0 as nat, record.1),
                }
            },
        }
    }
}

pub(crate) proof fn part2_general_records_step(
    records: Seq<(u16, ColorDefinition)>, colors: usize,
    initial: Seq<Part2TypedComponentOutput>, count: nat,
)
    ensures part2_general_records_prefix(records, colors, initial, count + 1)
        == match part2_general_records_prefix(records, colors, initial, count) {
            Err(error) => Err(error),
            Ok(previous) => match part2_general_validate_definition(records[count as int].1, colors) {
                Err(error) => Err(error),
                Ok(()) => part2_general_append_definition(previous, records[count as int].0 as nat, records[count as int].1),
            },
        },
{
    reveal(part2_general_records_prefix);
}

pub open spec fn part2_general_default_colors(
    initial: Seq<Part2TypedComponentOutput>, count: nat,
) -> Seq<Part2TypedComponentOutput> {
    Seq::new(initial.len(), |i: int|
        (initial[i].0, if i < count {
            initial[i].1.push((crate::ChannelType::Color, crate::ChannelAssociation::Color((i + 1) as u16)))
        } else { initial[i].1 }))
}

#[verifier::opaque]
pub open spec fn part2_general_definitions(
    config: Part2GeneralLayerConfig, colors: usize, input: Seq<Part2TypedComponentOutput>,
) -> Result<Seq<Part2TypedComponentOutput>, crate::DecodeError> {
    let cleared = part2_general_clear_definitions(input, input.len());
    if config.definitions.len() > 0 {
        part2_general_records_prefix(config.definitions, colors, cleared, config.definitions.len())
    } else {
        match config.opacity {
            None => Ok(input),
            Some(opacity) => {
                if input.len() < colors { Err(part2_composition_error(false)) }
                else {
                    let components = part2_general_default_colors(cleared, colors as nat);
                    match opacity {
                        Part2SourceOpacity::ChromaKey { .. } => Ok(components),
                        _ => {
                            if colors as nat + 1 > usize::MAX as nat { Err(part2_composition_error(true)) }
                            else if input.len() != colors as nat + 1 { Err(part2_composition_error(false)) }
                            else { part2_general_append_definition(components, colors as nat,
                                (if opacity == Part2SourceOpacity::Premultiplied {
                                    crate::ChannelType::PremultipliedOpacity
                                } else { crate::ChannelType::Opacity }, crate::ChannelAssociation::WholeImage)) }
                        },
                    }
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_general_finish(
    config: Part2GeneralLayerConfig, colors: usize, width: u32, height: u32,
    components: Part2GeneralComponents, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    match part2_general_definitions(config, colors, components.0) {
        Err(error) => Err(error),
        Ok(defined) => match part2_typed_image_from_parts(width, height, 0, 0, defined,
            crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)) {
            Err(error) => Err(error),
            Ok(image) => match color_convert_jp2(image.1, image.2, image.0, config.color,
                crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)) {
                Err(error) => Err(error),
                Ok(converted) => match part2_owned_layer_input(converted.0, converted.1, converted.2, converted.4) {
                    Err(error) => Err(error),
                    Ok(owned) => match config.opacity {
                        Some(Part2SourceOpacity::ChromaKey { channels, values }) => {
                            if channels as usize != colors || components.1.len() < colors {
                                Err(part2_composition_error(false))
                            } else {
                                match part2_normalized_component_chroma_keys(values, components.1.take(colors as int)) {
                                    Err(error) => Err(error),
                                    Ok(keys) => {
                                        let applied = part2_apply_chroma_key(owned, keys);
                                        match applied.0 { Err(error) => Err(error), Ok(()) => Ok(applied.1) }
                                    },
                                }
                            }
                        },
                        _ => Ok(owned),
                    },
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_general_after_assembly(
    config: Part2GeneralLayerConfig, colors: usize, width: u32, height: u32,
    result: Result<Part2GeneralComponents, crate::DecodeError>, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    match result {
        Err(error) => Err(error),
        Ok(components) => {
            if components.0.len() > crate::limits::resource_component_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Components,
                    limit: crate::limits::resource_component_limit(limits) as u64,
                    actual: components.0.len() as u64 })
            } else { part2_general_finish(config, colors, width, height, components, limits) }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_decode_general_layer(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    match part2_general_color_count(config.color) {
        Err(error) => Err(error),
        Ok(colors) => match part2_general_sources_prefix(file, config, layer_index, limits, part2_general_source_count(config)) {
            Err(error) => Err(error),
            Ok(sources) => {
                let width = sources.1;
                let height = sources.2;
                if width == 0 || height == 0 || width == u32::MAX || height == u32::MAX {
                    Err(part2_composition_error(false))
                } else if width as nat * height as nat > crate::limits::resource_pixel_limit(limits) {
                    Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Pixels,
                        limit: crate::limits::resource_pixel_limit(limits), actual: (width as nat * height as nat) as u64 })
                } else {
                    part2_general_after_assembly(config, colors, width, height,
                        part2_general_assembled_sources_prefix(sources.0, config, width, height, sources.0.len()), limits)
                }
            },
        },
    }
}

pub(crate) proof fn part2_general_sources_error(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, layer_index: usize,
    limits: &crate::ResourceLimits, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_general_sources_prefix(file, config, layer_index, limits, count) {
        Err(error) => part2_general_sources_prefix(file, config, layer_index, limits, total) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_general_sources_prefix);
    if count < total {
        part2_general_sources_error(file, config, layer_index, limits, count, (total - 1) as nat);
    }
}

pub(crate) proof fn part2_general_components_error(
    source: Part2GeneralSource, config: Part2GeneralLayerConfig, width: u32, height: u32,
    initial: Part2GeneralComponents, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_general_components_prefix(source, config, width, height, count, initial) {
        Err(error) => part2_general_components_prefix(source, config, width, height, total, initial) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_general_components_prefix);
    if count < total {
        part2_general_components_error(source, config, width, height, initial, count, (total - 1) as nat);
    }
}

pub(crate) proof fn part2_general_assembled_sources_error(
    sources: Seq<Part2GeneralSource>, config: Part2GeneralLayerConfig, width: u32, height: u32, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_general_assembled_sources_prefix(sources, config, width, height, count) {
        Err(error) => part2_general_assembled_sources_prefix(sources, config, width, height, total) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_general_assembled_sources_prefix);
    if count < total {
        part2_general_assembled_sources_error(sources, config, width, height, count, (total - 1) as nat);
    }
}

pub(crate) proof fn part2_general_records_error(
    records: Seq<(u16, ColorDefinition)>, colors: usize,
    initial: Seq<Part2TypedComponentOutput>, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_general_records_prefix(records, colors, initial, count) {
        Err(error) => part2_general_records_prefix(records, colors, initial, total) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_general_records_prefix);
    if count < total {
        part2_general_records_error(records, colors, initial, count, (total - 1) as nat);
    }
}

}
