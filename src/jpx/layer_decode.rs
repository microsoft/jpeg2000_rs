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
    TypedComponent, TypedSamples, jp2,
};
#[cfg(verus_keep_ghost)]
use super::{
    general_source_views, general_source_views_push, layer_borrowed_planes, layer_channels_outcome,
    layer_owned_planes_push, owned_layer_outcome, owned_layer_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures owned_layer_outcome(result) == crate::specs::part2_decode_effective_layer(
        jp2::jpx_file_decode_view(file), jp2::source_file_layer_configs(file), layer_index,
        crate::options::decode_options_limits(options)),
))]
pub(super) fn decode_effective_layer(
    file: &Jp2File<'_>,
    layer_index: usize,
    options: &DecodeOptions,
) -> Result<OwnedLayer, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_decode_effective_layer);
    }
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::converted_image_result(result) == crate::specs::part2_decode_jpx_layer(
        jp2::jpx_file_decode_view(file), codestream_index,
        jp2::optional_color_specification_method(color_override), crate::options::decode_options_limits(options)),
))]
pub(super) fn decode_layer(
    file: &Jp2File<'_>,
    codestream_index: usize,
    color_override: Option<&jp2::ColorSpecification>,
    options: &DecodeOptions,
) -> Result<ConvertedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::decode::associated_typed_errors_known();
        crate::specs::part2_decode_jpx_layer_unfold(
            jp2::jpx_file_decode_view(file), codestream_index,
            jp2::optional_color_specification_method(color_override), crate::options::decode_options_limits(options));
    }
    let (decoded, header) = crate::decode::decode_jpx_file(file, codestream_index, options)?;
    #[cfg(verus_keep_ghost)]
    proof! { crate::decode::associated_typed_success_known(&decoded, header); }
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
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::color::converted_image_result(result)
            == crate::specs::part2_owned_layer_image(owned_layer_view(&self)),
    ))]
    pub(super) fn into_image(self) -> Result<ConvertedImage, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost input = owned_layer_view(&self); }
        let pixels = checked_area(self.width, self.height)?;
        let (alpha, premultiplied) = match self.alpha {
            Some(value) => value,
            None => (vec![u16::MAX; pixels], false),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            if input.4.is_none() {
                assert(alpha@ =~= Seq::new(pixels as nat, |_i: int| u16::MAX));
            }
        }
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures owned_layer_outcome(result) == crate::specs::part2_decode_compositing_layer(
        jp2::jpx_file_decode_view(file), jp2::general_layer_config(file, layer),
        jp2::source_layer_color_override(layer), jp2::source_layer_geometry(layer), layer_index,
        crate::options::decode_options_limits(options)),
))]
fn decode_compositing_layer(
    file: &Jp2File<'_>,
    layer: &CompositingLayer<'_>,
    layer_index: usize,
    options: &DecodeOptions,
) -> Result<OwnedLayer, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_decode_compositing_layer);
    }
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures owned_layer_outcome(result) == crate::specs::part2_decode_general_layer(
        jp2::jpx_file_decode_view(file), jp2::general_layer_config(file, layer), layer_index,
        crate::options::decode_options_limits(options)),
))]
fn decode_general_compositing_layer(
    file: &Jp2File<'_>,
    layer: &CompositingLayer<'_>,
    layer_index: usize,
    options: &DecodeOptions,
) -> Result<OwnedLayer, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost config = jp2::general_layer_config(file, layer);
        let ghost input = jp2::jpx_file_decode_view(file);
        let ghost limits = crate::options::decode_options_limits(options);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::decode::associated_typed_outcome_known();
        reveal(crate::specs::part2_general_sources_prefix);
        reveal(crate::specs::part2_decode_general_layer);
    }
    let color = layer.color_group().first().unwrap_or(&file.header().color);
    let color_count = layer_color_count(color)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(color_count == 1 || color_count == 3);
    }
    let source_count = if layer.registrations().is_empty() {
        1
    } else {
        layer.registrations().len()
    };
    let mut sources = Vec::with_capacity(source_count);
    let mut width = u32::MAX;
    let mut height = u32::MAX;
    let mut source_index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(general_source_views(sources@) =~= Seq::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant source_index <= source_count,
                crate::specs::part2_general_color_count(config.color) == Ok(color_count),
                source_count == crate::specs::part2_general_source_count(config),
                sources.len() == source_index,
                config == jp2::general_layer_config(file, layer),
                input == jp2::jpx_file_decode_view(file),
                limits == crate::options::decode_options_limits(options),
                crate::specs::part2_general_sources_prefix(input, config, layer_index, limits, source_index as nat)
                    == Ok((general_source_views(sources@), width, height)),
            decreases source_count - source_index,
        )
    )]
    while source_index < source_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_decode_general_layer);
            crate::decode::associated_typed_outcome_known();
            crate::specs::part2_general_sources_step(input, config, layer_index, limits, source_index as nat);
            crate::specs::part2_general_sources_error(
                input, config, layer_index, limits, source_index as nat + 1, source_count as nat);
            reveal(crate::specs::part2_general_source_step);
        }
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
        #[cfg(verus_keep_ghost)]
        proof! {
            general_source_views_push(sources@, (image, horizontal_subsampling,
                vertical_subsampling, horizontal_offset, vertical_offset));
        }
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
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(width as nat * height as nat <= u64::MAX as nat) by(nonlinear_arith);
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
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_general_assembled_sources_prefix);
        assert(crate::image::typed_components_output_view(components@) =~= Seq::empty());
        assert(crate::specs::part2_decode_general_layer(input, config, layer_index, limits)
            == crate::specs::part2_general_after_assembly(config, color_count, width, height,
                crate::specs::part2_general_assembled_sources_prefix(
                    general_source_views(sources@), config, width, height, sources.len() as nat), limits));
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant source_index <= sources.len(),
                config == jp2::general_layer_config(file, layer),
                input == jp2::jpx_file_decode_view(file),
                limits == crate::options::decode_options_limits(options),
                crate::specs::part2_decode_general_layer(input, config, layer_index, limits)
                    == crate::specs::part2_general_after_assembly(config, color_count, width, height,
                        crate::specs::part2_general_assembled_sources_prefix(
                            general_source_views(sources@), config, width, height, sources.len() as nat), limits),
                crate::specs::part2_general_assembled_sources_prefix(
                    general_source_views(sources@), config, width, height, source_index as nat)
                    == Ok((crate::image::typed_components_output_view(components@), descriptors@)),
            decreases sources.len() - source_index,
        )
    )]
    while source_index < sources.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_general_after_assembly);
            crate::specs::part2_general_assembled_sources_step(
                general_source_views(sources@), config, width, height, source_index as nat);
            crate::specs::part2_general_assembled_sources_error(
                general_source_views(sources@), config, width, height, source_index as nat + 1, sources.len() as nat);
            reveal(crate::specs::part2_general_components_prefix);
        }
        let (
            image,
            horizontal_subsampling,
            vertical_subsampling,
            horizontal_offset,
            vertical_offset,
        ) = sources.get(source_index).ok_or_else(invalid_layer)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source = general_source_views(sources@)[source_index as int];
            let ghost initial = (crate::image::typed_components_output_view(components@), descriptors@);
        }
        let mut component_index = 0_usize;
        let component_count = image.components().len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component_index <= component_count,
                    source_index < sources.len(),
                    source == general_source_views(sources@)[source_index as int],
                    crate::specs::part2_general_assembled_sources_prefix(
                        general_source_views(sources@), config, width, height, source_index as nat) == Ok(initial),
                    input == jp2::jpx_file_decode_view(file),
                    limits == crate::options::decode_options_limits(options),
                    crate::specs::part2_decode_general_layer(input, config, layer_index, limits)
                        == crate::specs::part2_general_after_assembly(config, color_count, width, height,
                            crate::specs::part2_general_assembled_sources_prefix(
                                general_source_views(sources@), config, width, height, sources.len() as nat), limits),
                    component_count == source.0.1.len(),
                    source == (crate::image::typed_image_value_view(*image),
                        *horizontal_subsampling, *vertical_subsampling, *horizontal_offset, *vertical_offset),
                    config == jp2::general_layer_config(file, layer),
                    crate::specs::part2_general_components_prefix(
                        source, config, width, height, component_index as nat, initial)
                        == Ok((crate::image::typed_components_output_view(components@), descriptors@)),
                decreases component_count - component_index,
            )
        )]
        while component_index < component_count {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous = (crate::image::typed_components_output_view(components@), descriptors@);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_general_after_assembly);
                crate::specs::part2_general_assembled_sources_step(
                    general_source_views(sources@), config, width, height, source_index as nat);
                crate::specs::part2_general_assembled_sources_error(
                    general_source_views(sources@), config, width, height, source_index as nat + 1, sources.len() as nat);
                crate::specs::part2_general_components_step(
                    source, config, width, height, component_index as nat, initial);
                crate::specs::part2_general_components_error(
                    source, config, width, height, initial, component_index as nat + 1, component_count as nat);
                reveal(crate::specs::part2_general_component_step);
            }
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
            let mut assembled = crate::image::typed_component_from_parts(
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
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost assembled_value = crate::image::typed_component_output_view(&assembled).0;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                match assembled_value.samples {
                    crate::specs::Part1TypedSampleSequence::Unsigned(values) => {
                        assert(values =~= Seq::new(samples.len() as nat, |i: int| samples@[i] as u64));
                    },
                    crate::specs::Part1TypedSampleSequence::Signed(_) => { assert(false); },
                }
                assert(crate::specs::part2_general_component_step(
                    source, config, width, height, component_index as nat, previous)
                    == Ok((previous.0.push((assembled_value, source.0.2[component_index as int])),
                        previous.1.push((crate::image::typed_component_view(component).info.precision,
                            crate::image::typed_component_view(component).info.signed)))));
            }
            let mut definition_index = 0_usize;
            let definition_count = component.channel_definitions().len();
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant definition_index <= definition_count,
                        definition_count == crate::image::typed_component_definitions(component).len(),
                        crate::image::typed_component_output_view(&assembled).0 == assembled_value,
                        crate::image::typed_component_output_view(&assembled).1
                            == crate::image::typed_component_output_view(component).1.take(definition_index as int),
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
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::image::typed_component_output_view(&assembled).1
                        =~= crate::image::typed_component_output_view(component).1.take(definition_index as int));
                }
            }

            descriptors.push((component.info().precision, component.info().signed));
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_components = crate::image::typed_components_output_view(components@);
                let ghost assembled_output = crate::image::typed_component_output_view(&assembled);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(assembled_output.0 == assembled_value);
                assert(assembled_output.1 =~= source.0.2[component_index as int]);
                assert(previous_components == previous.0);
                assert(descriptors@ == previous.1.push((
                    crate::image::typed_component_view(component).info.precision,
                    crate::image::typed_component_view(component).info.signed)));
                assert(crate::specs::part2_general_component_step(
                    source, config, width, height, component_index as nat, previous)
                    == Ok((previous_components.push(assembled_output), descriptors@)));
            }
            components.push(assembled);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::image::typed_components_output_view(components@)
                    =~= previous_components.push(assembled_output));
            }
            component_index = component_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        source_index = source_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_general_after_assembly); }
    if components.len() > usize::from(options.limits().maximum_components()) {
        return Err(DecodeError::limit(
            Resource::Components,
            u64::from(options.limits().maximum_components()),
            components.len() as u64,
        ));
    }

    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost undefined = crate::image::typed_components_output_view(components@); }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_general_definitions);
        reveal(crate::specs::part2_general_finish);
    }
    if !layer.channel_definition_records().is_empty() {
        clear_channel_definitions(&mut components);
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_general_records_prefix); }
        let mut record_index = 0_usize;
        let record_count = layer.channel_definition_records().len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant record_index <= record_count,
                    input == jp2::jpx_file_decode_view(file),
                    limits == crate::options::decode_options_limits(options),
                    crate::specs::part2_decode_general_layer(input, config, layer_index, limits)
                        == crate::specs::part2_general_finish(config, color_count, width, height, (undefined, descriptors@), limits),
                    record_count == config.definitions.len(),
                    config == jp2::general_layer_config(file, layer),
                    crate::specs::part2_general_records_prefix(config.definitions, color_count,
                        crate::specs::part2_general_clear_definitions(undefined, undefined.len()), record_index as nat)
                        == Ok(crate::image::typed_components_output_view(components@)),
                decreases record_count - record_index,
            )
        )]
        while record_index < record_count {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = components@; }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_general_finish);
                reveal(crate::specs::part2_general_definitions);
                crate::specs::part2_general_records_step(config.definitions, color_count,
                    crate::specs::part2_general_clear_definitions(undefined, undefined.len()), record_index as nat);
                crate::specs::part2_general_records_error(config.definitions, color_count,
                    crate::specs::part2_general_clear_definitions(undefined, undefined.len()), record_index as nat + 1, record_count as nat);
            }
            let record = layer
                .channel_definition_records()
                .get(record_index)
                .ok_or_else(invalid_layer)?;
            validate_layer_definition(record.definition, color_count)?;
            components
                .get_mut(usize::from(record.channel))
                .ok_or_else(invalid_layer)?
                .add_channel_definition(record.definition);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::image::typed_components_output_view(components@)
                    =~= crate::image::typed_components_output_view(before).update(record.channel as int,
                        (crate::image::typed_components_output_view(before)[record.channel as int].0,
                            crate::image::typed_components_output_view(before)[record.channel as int].1.push(
                                crate::image::channel_definition_view(record.definition)))));
            }
            record_index = record_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
    } else if let Some(opacity) = layer.opacity() {
        #[cfg(verus_keep_ghost)]
        proof! { jp2::source_opacity_known(opacity); }
        clear_channel_definitions(&mut components);
        if components.len() < color_count {
            return Err(invalid_layer());
        }
        let mut color_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::image::typed_components_output_view(components@)
                =~= crate::specs::part2_general_default_colors(
                    crate::specs::part2_general_clear_definitions(undefined, undefined.len()), 0));
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant color_index <= color_count,
                input == jp2::jpx_file_decode_view(file),
                limits == crate::options::decode_options_limits(options),
                config == jp2::general_layer_config(file, layer),
                config.definitions.len() == 0,
                config.opacity == Some(jp2::source_opacity_value_view(opacity)),
                crate::specs::part2_decode_general_layer(input, config, layer_index, limits)
                    == crate::specs::part2_general_finish(config, color_count, width, height, (undefined, descriptors@), limits),
                    color_count <= components.len(), color_count <= u16::MAX,
                components.len() == undefined.len(),
                    crate::image::typed_components_output_view(components@)
                        == crate::specs::part2_general_default_colors(
                            crate::specs::part2_general_clear_definitions(undefined, undefined.len()), color_index as nat),
                decreases color_count - color_index,
            )
        )]
        while color_index < color_count {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = components@; }
            components
                .get_mut(color_index)
                .ok_or_else(invalid_layer)?
                .add_channel_definition(crate::image::channel_definition_new(
                    ChannelType::Color,
                    ChannelAssociation::Color(
                        u16::try_from(color_index + 1).map_err(|_| arithmetic_overflow())?,
                    ),
                ));
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::image::typed_components_output_view(components@)[color_index as int]
                    == (crate::image::typed_components_output_view(before)[color_index as int].0,
                        crate::image::typed_components_output_view(before)[color_index as int].1.push((
                            ChannelType::Color, ChannelAssociation::Color((color_index + 1) as u16)))));
                assert forall|i: int| 0 <= i < components.len() implies
                    #[trigger] crate::image::typed_components_output_view(components@)[i]
                        == crate::specs::part2_general_default_colors(
                            crate::specs::part2_general_clear_definitions(undefined, undefined.len()), color_index as nat + 1)[i] by {
                    if i != color_index as int {
                        assert(components@[i] == before[i]);
                        assert(crate::image::typed_component_output_view(&before[i])
                            == crate::specs::part2_general_default_colors(
                                crate::specs::part2_general_clear_definitions(undefined, undefined.len()), color_index as nat)[i]);
                    }
                }
                assert(crate::image::typed_components_output_view(components@)
                    =~= crate::specs::part2_general_default_colors(
                        crate::specs::part2_general_clear_definitions(undefined, undefined.len()), color_index as nat + 1));
            }
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
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = components@; }
            components
                .get_mut(color_count)
                .ok_or_else(invalid_layer)?
                .add_channel_definition(crate::image::channel_definition_new(
                    if matches!(opacity, LayerOpacity::Premultiplied) {
                        ChannelType::PremultipliedOpacity
                    } else {
                        ChannelType::Opacity
                    },
                    ChannelAssociation::WholeImage,
                ));
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::image::typed_components_output_view(components@)
                    =~= crate::image::typed_components_output_view(before).update(color_count as int,
                        (crate::image::typed_components_output_view(before)[color_count as int].0,
                            crate::image::typed_components_output_view(before)[color_count as int].1.push((
                                if matches!(opacity, LayerOpacity::Premultiplied) {
                                    ChannelType::PremultipliedOpacity
                                } else { ChannelType::Opacity }, ChannelAssociation::WholeImage)))));
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_general_finish);
        reveal(crate::specs::part2_general_definitions);
        assert(crate::specs::part2_general_definitions(config, color_count, undefined)
            == Ok(crate::image::typed_components_output_view(components@)));
    }

    let assembled = crate::image::typed_image_from_components_with_origin(
        width,
        height,
        0,
        0,
        components,
        options.limits(),
    )?;
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_general_color_count(jp2::color_specification_method(color)),
))]
fn layer_color_count(color: &jp2::ColorSpecification) -> Result<usize, DecodeError> {
    match color.method() {
        jp2::ColorMethod::Unspecified => Err(DecodeError::UnsupportedColorConversion {
            reason: crate::UnsupportedColorConversion::UnspecifiedColorSpace,
        }),
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

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures crate::image::typed_components_output_view(final(components)@)
        == crate::specs::part2_general_clear_definitions(
            crate::image::typed_components_output_view(old(components)@), old(components)@.len()),
))]
fn clear_channel_definitions(components: &mut [TypedComponent]) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input = crate::image::typed_components_output_view(components@); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::image::typed_components_output_view(components@)
            =~= crate::specs::part2_general_clear_definitions(input, 0));
    }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= components.len(),
                input.len() == components.len(),
                input == crate::image::typed_components_output_view(old(components)@),
                crate::image::typed_components_output_view(components@)
                    == crate::specs::part2_general_clear_definitions(input, index as nat),
            decreases components.len() - index,
        )
    )]
    while index < components.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = components@; }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::image::typed_components_output_view(components@)[index as int].0 == input[index as int].0);
        }
        if let Some(component) = components.get_mut(index) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::image::typed_component_output_view(component).0 == input[index as int].0);
            }
            component.clear_channel_definitions();
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::image::typed_component_output_view(component).1 =~= Seq::empty());
                assert(crate::image::typed_component_output_view(component) == (input[index as int].0, Seq::empty()));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|i: int| 0 <= i < components.len() implies
                #[trigger] crate::image::typed_components_output_view(components@)[i]
                    == crate::specs::part2_general_clear_definitions(input, index as nat + 1)[i] by {
                if i == index as int {
                    assert(crate::image::typed_components_output_view(components@)[i].1 =~= Seq::empty());
                    assert(crate::image::typed_components_output_view(components@)[i].0 == input[i].0);
                } else {
                    assert(components@[i] == before[i]);
                    assert(crate::image::typed_component_output_view(&before[i])
                        == crate::specs::part2_general_clear_definitions(input, index as nat)[i]);
                }
            }
            assert(crate::image::typed_components_output_view(components@)
                =~= crate::specs::part2_general_clear_definitions(input, index as nat + 1));
        }
        index += 1;
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_general_validate_definition(
        crate::image::channel_definition_view(definition), color_count),
))]
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
