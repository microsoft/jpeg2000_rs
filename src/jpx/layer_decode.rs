//! Codestream decoding and compositing-layer channel definitions.
use super::channels::layer_channels;
use super::chroma::{apply_chroma_key, normalized_chroma_keys_for_components};
use super::opacity::apply_layer_opacity;
use super::registration::{register_layer, register_samples};
use super::resources::{
    arithmetic_overflow, checked_area, copy_samples, enforce_limit, invalid_layer,
    registered_extent,
};
use super::{
    ChannelAssociation, ChannelDefinition, ChannelType, ComponentInfo, CompositingLayer,
    ConvertedImage, DecodeError, DecodeOptions, Jp2File, LayerOpacity, OwnedLayer, Resource,
    TypedComponent, TypedImage, TypedSamples, jp2,
};
#[cfg(verus_keep_ghost)]
use super::{
    layer_borrowed_planes, layer_channels_outcome, layer_owned_planes_push, owned_layer_outcome,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) fn decode_effective_layer(
    file: &Jp2File<'_>,
    layer_index: usize,
    options: &DecodeOptions,
) -> Result<OwnedLayer, DecodeError> {
    if file.compositing_layers().is_empty() {
        if layer_index >= file.codestream_count() {
            return Err(DecodeError::LayerIndexOutOfRange {
                index: layer_index,
                layers: file.codestream_count(),
            });
        }
        return owned_layer_from_image(&decode_layer(file, layer_index, None, options)?);
    }
    let layer = file.compositing_layer(layer_index)?;
    decode_compositing_layer(file, layer, layer_index, options)
}

pub(super) fn decode_layer(
    file: &Jp2File<'_>,
    codestream_index: usize,
    color_override: Option<&jp2::ColorSpecification>,
    options: &DecodeOptions,
) -> Result<ConvertedImage, DecodeError> {
    let (decoded, header) = crate::decode::decode_jpx_file(file, codestream_index, options)?;
    let header = header.unwrap_or(file.header());
    crate::color::convert_jp2_color(
        &decoded,
        color_override.unwrap_or(&header.color),
        options.limits(),
    )
}

#[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures owned_layer_outcome(result) == crate::specs::part2_owned_layer_input(
                crate::color::converted_image_view(image).0, crate::color::converted_image_view(image).1,
                crate::color::converted_image_view(image).2,
                crate::color::converted_channel_views(crate::color::converted_image_view(image).4),
            ),
        )
    )]
pub(super) fn owned_layer_from_image(image: &ConvertedImage) -> Result<OwnedLayer, DecodeError> {
    let channels = layer_channels(image)?;
    let mut colors = Vec::with_capacity(channels.colors.len());
    let mut index = 0_usize;
    #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= channels.colors.len(),
                    colors.len() == index,
                    layer_channels_outcome(Ok(channels)) == crate::specs::part2_layer_input(
                        crate::color::converted_image_view(image).0, crate::color::converted_image_view(image).1,
                        crate::color::converted_image_view(image).2,
                        crate::color::converted_channel_views(crate::color::converted_image_view(image).4),
                    ),
                    crate::specs::part2_composition_planes(colors@)
                        == layer_borrowed_planes(channels.colors@).take(index as int),
                decreases channels.colors.len() - index,
            )
        )]
    while index < channels.colors.len() {
        let samples = *channels.colors.get(index).ok_or_else(invalid_layer)?;
        let copied = copy_samples(samples)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(samples@ == layer_borrowed_planes(channels.colors@)[index as int]);
            assert(copied@ == samples@);
            layer_owned_planes_push(colors@, copied);
        }
        colors.push(copied);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_composition_planes(colors@)
                =~= layer_borrowed_planes(channels.colors@).take(index as int + 1));
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_composition_planes(colors@) =~= layer_borrowed_planes(channels.colors@));
    }
    Ok(OwnedLayer {
        width: channels.width,
        height: channels.height,
        color_space: image.color_space(),
        colors,
        alpha: channels.alpha,
    })
}

impl OwnedLayer {
    pub(super) fn into_image(self) -> Result<ConvertedImage, DecodeError> {
        let pixels = checked_area(self.width, self.height)?;
        let (alpha, premultiplied) = match self.alpha {
            Some(value) => value,
            None => (vec![u16::MAX; pixels], false),
        };
        crate::color::from_layer(
            self.width,
            self.height,
            self.color_space,
            self.colors,
            alpha,
            premultiplied,
        )
    }
}

fn decode_compositing_layer(
    file: &Jp2File<'_>,
    layer: &CompositingLayer<'_>,
    layer_index: usize,
    options: &DecodeOptions,
) -> Result<OwnedLayer, DecodeError> {
    if !layer.channel_definition_records().is_empty()
        || layer.registrations().len() > 1
        || matches!(layer.opacity(), Some(LayerOpacity::ChromaKey { .. }))
    {
        return decode_general_compositing_layer(file, layer, layer_index, options);
    }
    let color_override = layer.color_group().first();
    if layer.registrations().is_empty() {
        let image = decode_layer(file, layer_index, color_override, options)?;
        let mut owned = owned_layer_from_image(&image)?;
        apply_layer_opacity(file, layer, layer_index, &mut owned, None, options)?;
        return Ok(owned);
    }
    let first = layer
        .registrations()
        .first()
        .ok_or_else(arithmetic_overflow)?;
    let image = decode_layer(
        file,
        usize::from(first.codestream_index),
        color_override,
        options,
    )?;
    let owned = owned_layer_from_image(&image)?;
    let mut registered = register_layer(
        &owned,
        first,
        layer.horizontal_grid_size(),
        layer.vertical_grid_size(),
    )?;
    let alpha_registration = layer.registrations().get(1);
    apply_layer_opacity(
        file,
        layer,
        usize::from(first.codestream_index),
        &mut registered,
        alpha_registration,
        options,
    )?;
    Ok(registered)
}

fn decode_general_compositing_layer(
    file: &Jp2File<'_>,
    layer: &CompositingLayer<'_>,
    layer_index: usize,
    options: &DecodeOptions,
) -> Result<OwnedLayer, DecodeError> {
    let color = layer.color_group().first().unwrap_or(&file.header().color);
    let color_count = layer_color_count(color)?;
    let source_count = if layer.registrations().is_empty() {
        1
    } else {
        layer.registrations().len()
    };
    let mut sources = Vec::with_capacity(source_count);
    let mut width = u32::MAX;
    let mut height = u32::MAX;
    let mut source_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant source_index <= source_count,
            decreases source_count - source_index,
        )
    )]
    while source_index < source_count {
        let (
            codestream_index,
            horizontal_subsampling,
            vertical_subsampling,
            horizontal_offset,
            vertical_offset,
        ) = if layer.registrations().is_empty() {
            (layer_index, 1_u8, 1_u8, 0_u32, 0_u32)
        } else {
            let registration = layer
                .registrations()
                .get(source_index)
                .ok_or_else(invalid_layer)?;
            (
                usize::from(registration.codestream_index),
                registration.horizontal_subsampling,
                registration.vertical_subsampling,
                registration.horizontal_offset,
                registration.vertical_offset,
            )
        };
        let (image, _) = crate::decode::decode_jpx_file(file, codestream_index, options)?;
        let registered_width = registered_extent(
            image.width(),
            u32::from(horizontal_subsampling),
            u32::from(layer.horizontal_grid_size()),
            horizontal_offset,
        )?;
        let registered_height = registered_extent(
            image.height(),
            u32::from(vertical_subsampling),
            u32::from(layer.vertical_grid_size()),
            vertical_offset,
        )?;
        width = width.min(registered_width);
        height = height.min(registered_height);
        sources.push((
            image,
            horizontal_subsampling,
            vertical_subsampling,
            horizontal_offset,
            vertical_offset,
        ));
        source_index = source_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    if width == 0 || height == 0 || width == u32::MAX || height == u32::MAX {
        return Err(invalid_layer());
    }
    enforce_limit(
        Resource::Pixels,
        options.limits().maximum_pixels(),
        u64::from(width)
            .checked_mul(u64::from(height))
            .ok_or_else(arithmetic_overflow)?,
    )?;

    let mut components = Vec::new();
    let mut descriptors = Vec::new();
    source_index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant source_index <= sources.len(),
            decreases sources.len() - source_index,
        )
    )]
    while source_index < sources.len() {
        let (
            image,
            horizontal_subsampling,
            vertical_subsampling,
            horizontal_offset,
            vertical_offset,
        ) = sources.get(source_index).ok_or_else(invalid_layer)?;
        let mut component_index = 0_usize;
        let component_count = image.components().len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component_index <= component_count,
                decreases component_count - component_index,
            )
        )]
        while component_index < component_count {
            let component = image
                .components()
                .get(component_index)
                .ok_or_else(invalid_layer)?;
            let normalized = crate::color::normalize_component(
                component,
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin(),
            )?;
            let samples = register_samples(
                &normalized,
                image.width(),
                image.height(),
                width,
                height,
                u32::from(*horizontal_subsampling),
                u32::from(*vertical_subsampling),
                u32::from(layer.horizontal_grid_size()),
                u32::from(layer.vertical_grid_size()),
                *horizontal_offset,
                *vertical_offset,
            )?;
            let mut assembled = TypedComponent::from_parts(
                width,
                height,
                ComponentInfo {
                    precision: 16,
                    signed: false,
                    x_subsampling: 1,
                    y_subsampling: 1,
                    x_registration: 0,
                    y_registration: 0,
                },
                TypedSamples::Unsigned(widen_samples(&samples)?),
            );
            let mut definition_index = 0_usize;
            let definition_count = component.channel_definitions().len();
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant definition_index <= definition_count,
                    decreases definition_count - definition_index,
                )
            )]
            while definition_index < definition_count {
                assembled.add_channel_definition(
                    *component
                        .channel_definitions()
                        .get(definition_index)
                        .ok_or_else(invalid_layer)?,
                );
                definition_index = definition_index
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }

            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(output =>
                    ensures match output {
                        Ok(values) => values@.len() == samples@.len()
                            && forall|i: int| 0 <= i < samples@.len()
                                ==> #[trigger] values@[i] == samples@[i] as u64,
                        Err(_) => false,
                    },
                )
            )]
            fn widen_samples(samples: &[u16]) -> Result<Vec<u64>, DecodeError> {
                let mut widened = Vec::with_capacity(samples.len());
                let mut index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant index <= samples.len(),
                            widened.len() == index,
                            forall|i: int| 0 <= i < index
                                ==> #[trigger] widened@[i] == samples@[i] as u64,
                        decreases samples.len() - index,
                    )
                )]
                while index < samples.len() {
                    widened.push(u64::from(*samples.get(index).ok_or_else(invalid_layer)?));
                    index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                Ok(widened)
            }
            descriptors.push((component.info().precision, component.info().signed));
            components.push(assembled);
            component_index = component_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        source_index = source_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    if components.len() > usize::from(options.limits().maximum_components()) {
        return Err(DecodeError::limit(
            Resource::Components,
            u64::from(options.limits().maximum_components()),
            components.len() as u64,
        ));
    }

    if !layer.channel_definition_records().is_empty() {
        clear_channel_definitions(&mut components);
        let mut record_index = 0_usize;
        let record_count = layer.channel_definition_records().len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant record_index <= record_count,
                decreases record_count - record_index,
            )
        )]
        while record_index < record_count {
            let record = layer
                .channel_definition_records()
                .get(record_index)
                .ok_or_else(invalid_layer)?;
            validate_layer_definition(record.definition, color_count)?;
            components
                .get_mut(usize::from(record.channel))
                .ok_or_else(invalid_layer)?
                .add_channel_definition(record.definition);
            record_index = record_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
    } else if let Some(opacity) = layer.opacity() {
        clear_channel_definitions(&mut components);
        if components.len() < color_count {
            return Err(invalid_layer());
        }
        let mut color_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant color_index <= color_count,
                decreases color_count - color_index,
            )
        )]
        while color_index < color_count {
            components
                .get_mut(color_index)
                .ok_or_else(invalid_layer)?
                .add_channel_definition(ChannelDefinition::new(
                    ChannelType::Color,
                    ChannelAssociation::Color(
                        u16::try_from(color_index + 1).map_err(|_| arithmetic_overflow())?,
                    ),
                ));
            color_index = color_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        if matches!(
            opacity,
            LayerOpacity::Straight | LayerOpacity::Premultiplied
        ) {
            let expected_channels = color_count.checked_add(1).ok_or_else(arithmetic_overflow)?;
            if components.len() != expected_channels {
                return Err(invalid_layer());
            }
            components
                .get_mut(color_count)
                .ok_or_else(invalid_layer)?
                .add_channel_definition(ChannelDefinition::new(
                    if matches!(opacity, LayerOpacity::Premultiplied) {
                        ChannelType::PremultipliedOpacity
                    } else {
                        ChannelType::Opacity
                    },
                    ChannelAssociation::WholeImage,
                ));
        }
    }

    let assembled =
        TypedImage::from_components_with_origin(width, height, 0, 0, components, options.limits())?;
    let converted = crate::color::convert_jp2_color(&assembled, color, options.limits())?;
    let mut owned = owned_layer_from_image(&converted)?;
    if let Some(LayerOpacity::ChromaKey { channels, values }) = layer.opacity() {
        if usize::from(*channels) != color_count || descriptors.len() < color_count {
            return Err(invalid_layer());
        }
        let keys = normalized_chroma_keys_for_components(
            values,
            descriptors.get(..color_count).ok_or_else(invalid_layer)?,
        )?;
        apply_chroma_key(&mut owned, &keys)?;
    }
    Ok(owned)
}

fn layer_color_count(color: &jp2::ColorSpecification) -> Result<usize, DecodeError> {
    match color.method() {
        jp2::ColorMethod::Enumerated {
            color_space: jp2::ENUMERATED_GRAYSCALE,
        } => Ok(1),
        jp2::ColorMethod::Enumerated {
            color_space: jp2::ENUMERATED_SRGB | jp2::ENUMERATED_SYCC,
        } => Ok(3),
        jp2::ColorMethod::RestrictedIcc { .. } | jp2::ColorMethod::AnyIcc { .. } => {
            Err(DecodeError::UnsupportedColorConversion {
                reason: crate::UnsupportedColorConversion::IccProfile,
            })
        }
        jp2::ColorMethod::Enumerated { .. } => Err(DecodeError::UnsupportedColorConversion {
            reason: crate::UnsupportedColorConversion::EnumeratedColorSpace,
        }),
    }
}

fn clear_channel_definitions(components: &mut [TypedComponent]) {
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= components.len(),
            decreases components.len() - index,
        )
    )]
    while index < components.len() {
        if let Some(component) = components.get_mut(index) {
            component.clear_channel_definitions();
        }
        index += 1;
    }
}

fn validate_layer_definition(
    definition: ChannelDefinition,
    color_count: usize,
) -> Result<(), DecodeError> {
    match definition.association() {
        ChannelAssociation::Color(value) if value == 0 || usize::from(value) > color_count => {
            Err(invalid_layer())
        }
        ChannelAssociation::Unassociated
            if matches!(definition.channel_type(), ChannelType::Color) =>
        {
            Err(invalid_layer())
        }
        _ => Ok(()),
    }
}
