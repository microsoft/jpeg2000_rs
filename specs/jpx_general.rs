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
        Ok(decoded) => match part2_native_registered_extent(decoded.0.0.0, selected.1 as u32, config.horizontal_grid as u32, selected.3) {
            Err(error) => Err(error),
            Ok(width) => match part2_native_registered_extent(decoded.0.0.1, selected.2 as u32, config.vertical_grid as u32, selected.4) {
                Err(error) => Err(error),
                Ok(height) => Ok((previous.0.push((decoded.0, selected.1, selected.2, selected.3, selected.4)),
                    if previous.1 < width { previous.1 } else { width },
                    if previous.2 < height { previous.2 } else { height })),
            },
        },
    }
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
