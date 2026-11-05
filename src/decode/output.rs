use super::{
    DecodeError, DecodeOptions, DecodeSelection, ImageSize, MalformedKind, ResourceLimits,
    SelectionError, TileSelection, TypedComponent, TypedImage, TypedSamples, ValidatedSelection,
    arithmetic_overflow, ceil_div_u32, codestream, decode_codestream, decode_layout_selected,
    invalid_decode, jp2, typed_layout, validate_selection,
};
#[cfg(verus_keep_ghost)]
use super::{associated_typed_outcome, color_selection_outcome, validated_selection_view};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) fn color_selection(
    input: &[u8],
    requested: &DecodeSelection,
    limits: &ResourceLimits,
) -> Result<(DecodeSelection, [u32; 4]), DecodeError> {
    let layout = codestream::parse_layout(input, limits)?;
    let size = &layout.info.image_size;
    color_selection_for_size(size, requested)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures color_selection_outcome(result) == crate::specs::part2_color_selection_requested(
        crate::codestream::selection_geometry_view(size), crate::codestream::image_size_component_infos(size),
        size.components, crate::options::decode_selection_view(requested),
    ),
))]
pub(super) fn color_selection_for_size(
    size: &ImageSize,
    requested: &DecodeSelection,
) -> Result<(DecodeSelection, [u32; 4]), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::selection_geometry_known_fields(size); }
    let validated = validate_selection(size, requested)?;
    color_selection_from_validated(size, validated)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures color_selection_outcome(result) == crate::specs::part2_color_selection_context(
        size.x_origin, size.y_origin, crate::codestream::image_size_component_infos(size), size.components,
        validated_selection_view(validated),
    ),
))]
pub(super) fn color_selection_from_validated(
    size: &ImageSize,
    validated: ValidatedSelection,
) -> Result<(DecodeSelection, [u32; 4]), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_color_target); }
    let discard_levels = validated.discard_levels;
    if discard_levels >= 32 {
        return Err(DecodeError::InvalidSelection {
            reason: SelectionError::ReductionTooLarge,
        });
    }
    let scale = 1_u32 << u32::from(discard_levels);
    let target = [
        ceil_div_u32(validated.region[0], scale)?,
        ceil_div_u32(validated.region[1], scale)?,
        ceil_div_u32(validated.region[2], scale)?,
        ceil_div_u32(validated.region[3], scale)?,
    ];
    let mut horizontal = 0_u32;
    let mut vertical = 0_u32;
    let mut component = 0_u16;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(scale == 1u32 << (discard_levels as u32));
        assert(crate::specs::part2_selection_ceil(validated.region[0], scale) == Ok(target[0]));
        assert(crate::specs::part2_selection_ceil(validated.region[1], scale) == Ok(target[1]));
        assert(crate::specs::part2_selection_ceil(validated.region[2], scale) == Ok(target[2]));
        assert(crate::specs::part2_selection_ceil(validated.region[3], scale) == Ok(target[3]));
        assert(target@ =~= seq![target[0], target[1], target[2], target[3]]);
        assert(crate::specs::part2_color_target(validated.region@, discard_levels) == Ok(target@));
        crate::proofs::production_impl::production_color_sampling_empty(
            crate::codestream::image_size_component_infos(size), size.components, target@);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= size.components,
            validated.discard_levels < 32,
            discard_levels == validated.discard_levels,
            scale == 1u32 << (discard_levels as u32),
            crate::specs::part2_color_target(validated.region@, discard_levels) == Ok(target@),
            crate::specs::part2_color_sampling_prefix(
                crate::codestream::image_size_component_infos(size), size.components, target@, component as nat,
            ) == Ok((horizontal, vertical)),
            decreases size.components - component,
        )
    )]
    while component < size.components {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_sampling_step(
                crate::codestream::image_size_component_infos(size), size.components, target@, component as nat);
            crate::proofs::production_impl::production_color_sampling_error_guard(
                crate::codestream::image_size_component_infos(size), size.components, target@, component as nat + 1, size.components as nat);
        }
        let info = codestream::image_component_info(size, component)?;
        let x_step = u64::from(info.x_subsampling)
            .checked_mul(65_536)
            .ok_or_else(arithmetic_overflow)?;
        let y_step = u64::from(info.y_subsampling)
            .checked_mul(65_536)
            .ok_or_else(arithmetic_overflow)?;
        let x = u64::from(target[0])
            .checked_mul(65_536)
            .ok_or_else(arithmetic_overflow)?
            .saturating_sub(u64::from(info.x_registration));
        let y = u64::from(target[1])
            .checked_mul(65_536)
            .ok_or_else(arithmetic_overflow)?
            .saturating_sub(u64::from(info.y_registration));
        if x.checked_rem(x_step).ok_or_else(invalid_decode)? != 0 {
            horizontal = horizontal.max(u32::from(info.x_subsampling));
        }
        if y.checked_rem(y_step).ok_or_else(invalid_decode)? != 0 {
            vertical = vertical.max(u32::from(info.y_subsampling));
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let x0 = validated.region[0]
        .saturating_sub(horizontal.saturating_mul(scale))
        .max(size.x_origin);
    let y0 = validated.region[1]
        .saturating_sub(vertical.saturating_mul(scale))
        .max(size.y_origin);
    // Retain resampling context across ROI/tile boundaries; validate the original selection first.
    let expanded = crate::options::selection_from_parts(
        TileSelection::All,
        Some(crate::ImageRegion {
            x: x0,
            y: y0,
            width: validated.region[2]
                .checked_sub(x0)
                .ok_or_else(arithmetic_overflow)?,
            height: validated.region[3]
                .checked_sub(y0)
                .ok_or_else(arithmetic_overflow)?,
        }),
        discard_levels,
    );
    Ok((expanded, target))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::color::converted_image_result(result) == crate::specs::color_convert_selected(
            crate::image::typed_image_component_views(image), crate::image::typed_image_definition_views(image),
            crate::image::typed_image_geometry(image), crate::jp2::color_specification_method(color), target,
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
        ),
    )
)]
pub(super) fn convert_selected_color(
    image: &TypedImage,
    color: &jp2::ColorSpecification,
    target: [u32; 4],
    limits: &ResourceLimits,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let converted = crate::color::convert_jp2_color(image, color, limits)?;
    converted.crop(
        target[0]
            .checked_sub(image.x_origin())
            .ok_or_else(invalid_decode)?,
        target[1]
            .checked_sub(image.y_origin())
            .ok_or_else(invalid_decode)?,
        target[2]
            .checked_sub(target[0])
            .ok_or_else(invalid_decode)?,
        target[3]
            .checked_sub(target[1])
            .ok_or_else(invalid_decode)?,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures associated_typed_outcome(result) == crate::specs::part2_apply_associated_output(
        crate::image::typed_image_value_view(decoded), jp2::associated_header_option(header),
        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn apply_associated_output<'a>(
    decoded: TypedImage,
    header: Option<&'a jp2::Jp2Header>,
    limits: &ResourceLimits,
) -> Result<(TypedImage, Option<&'a jp2::Jp2Header>), DecodeError> {
    let image = match header {
        Some(header) => apply_jp2_output(decoded, header, limits)?,
        None => decoded,
    };
    Ok((image, header))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::converted_image_result(result) == crate::specs::part2_convert_associated_selected(
        crate::image::typed_image_value_view(*image), jp2::associated_header_option(header), target,
        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
    ),
))]
pub(super) fn convert_associated_selected_color(
    image: &TypedImage,
    header: Option<&jp2::Jp2Header>,
    target: [u32; 4],
    limits: &ResourceLimits,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let header = match header {
        Some(header) => header,
        None => {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::MissingRequiredStructure,
            });
        }
    };
    convert_selected_color(image, &header.color, target, limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::converted_image_result(result) == crate::specs::part2_convert_associated(
        crate::image::typed_image_value_view(*image), jp2::associated_header_option(header),
        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
    ),
))]
pub(super) fn convert_associated_color(
    image: &TypedImage,
    header: Option<&jp2::Jp2Header>,
    limits: &ResourceLimits,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let header = match header {
        Some(header) => header,
        None => {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::MissingRequiredStructure,
            });
        }
    };
    crate::color::convert_jp2_color(image, &header.color, limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::converted_image_result(result) == crate::specs::part2_finish_associated_selected_output(
        crate::image::typed_image_value_view(decoded), jp2::associated_header_option(header), target,
        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
        crate::limits::resource_work_limit(limits),
    ),
))]
pub(super) fn finish_associated_selected_output(
    decoded: TypedImage,
    header: Option<&jp2::Jp2Header>,
    target: [u32; 4],
    limits: &ResourceLimits,
) -> Result<crate::color::ConvertedImage, DecodeError> {
    let (mapped, header) = apply_associated_output(decoded, header, limits)?;
    convert_associated_selected_color(&mapped, header, target, limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures associated_typed_outcome(result) == crate::specs::part2_decode_jpx_codestream(
        jp2::jpx_file_decode_view(file), codestream_index, crate::options::decode_options_limits(options)),
))]
pub(crate) fn decode_jpx_file<'a>(
    file: &'a jp2::Jp2File<'_>,
    codestream_index: usize,
    options: &DecodeOptions,
) -> Result<(TypedImage, Option<&'a jp2::Jp2Header>), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(associated_typed_outcome);
        codestream::complete_codestream_info_errors_known();
        crate::specs::part2_decode_jpx_codestream_unfold(
            jp2::jpx_file_decode_view(file), codestream_index, crate::options::decode_options_limits(options));
    }
    if !file.file_type().is_jpx_compatible() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }

    #[cfg(any())]
    fn decode_jpx_file_selected<'a>(
        file: &'a jp2::Jp2File<'_>,
        codestream_index: usize,
        options: &DecodeOptions,
        selection: &DecodeSelection,
    ) -> Result<(TypedImage, Option<&'a jp2::Jp2Header>), DecodeError> {
        if !file.file_type().is_jpx_compatible() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
        }
        let selected = file.codestream(codestream_index)?;
        let associated_header = Some(jp2::associated_header_for_codestream(
            selected,
            file.header(),
        )?);
        let layout = codestream::parse_layout(selected.data(), options.limits())?;
        if let Some(header) = associated_header {
            jp2::validate_selected_header(header, &layout.info, selected.box_header().offset())?;
        }
        let decoded = typed_layout(
            &layout,
            decode_layout_selected(&layout, selection, options.limits())?,
            options.limits(),
        )?;
        apply_associated_output(decoded, associated_header, options.limits())
    }
    let selected = file.codestream(codestream_index)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        jp2::codestream_source_known_fields(selected);
        crate::specs::part2_decode_jpx_source_unfold(
            jp2::codestream_source_view(selected), jp2::jpx_file_decode_view(file).2,
            crate::options::decode_options_limits(options));
    }
    let associated_header = Some(jp2::associated_header_for_codestream(
        selected,
        file.header(),
    )?);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_jpx_associated_unfold(
            jp2::codestream_source_view(selected), jp2::associated_header_view(associated_header.unwrap()),
            crate::options::decode_options_limits(options));
    }
    let info = codestream::parse(selected.data(), options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::complete_codestream_info_known_fields(&info);
    }
    if let Some(header) = associated_header {
        jp2::validate_selected_header(header, &info, selected.box_header().offset())?;
    }
    let decoded = decode_codestream(selected.data(), options)?;
    apply_associated_output(decoded, associated_header, options.limits())
}

pub(super) fn decode_jpx_file_selected<'a>(
    file: &'a jp2::Jp2File<'_>,
    codestream_index: usize,
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<(TypedImage, Option<&'a jp2::Jp2Header>), DecodeError> {
    if !file.file_type().is_jpx_compatible() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    let selected = file.codestream(codestream_index)?;
    let associated_header = match selected.codestream_header() {
        Some(association) => match association.parsed_header() {
            Some(header) => Some(header),
            None => {
                return Err(DecodeError::malformed(
                    association.box_header().offset(),
                    MalformedKind::MissingRequiredStructure,
                ));
            }
        },
        None => Some(file.header()),
    };
    let layout = codestream::parse_layout(selected.data(), options.limits())?;
    if let Some(header) = associated_header {
        jp2::validate_selected_header(header, &layout.info, selected.box_header().offset())?;
    }
    let decoded = typed_layout(
        &layout,
        decode_layout_selected(&layout, selection, options.limits())?,
        options.limits(),
    )?;
    let image = match associated_header {
        Some(header) => apply_jp2_output(decoded, header, options.limits())?,
        None => decoded,
    };
    Ok((image, associated_header))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_typed_image_outcome(result) == crate::specs::part2_apply_output_header(
        crate::image::typed_image_value_view(decoded), jp2::output_header_view(header),
        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn apply_jp2_output(
    decoded: TypedImage,
    header: &jp2::Jp2Header,
    limits: &ResourceLimits,
) -> Result<TypedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input_components = crate::image::typed_components_output_view(crate::image::typed_image_components(&decoded));
        let ghost raw_header = jp2::output_header_view(header);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(input_components =~= Seq::new(crate::image::typed_image_value_view(decoded).1.len(),
            |i: int| (crate::image::typed_image_value_view(decoded).1[i], crate::image::typed_image_value_view(decoded).2[i])));
    }
    let mut components = if header.component_mappings.is_empty() {
        let mut copied = Vec::with_capacity(decoded.components().len());
        let component_count = decoded.components().len();
        let mut component_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component_index <= component_count,
                component_count == input_components.len(),
                raw_header == jp2::output_header_view(header),
                raw_header.1.len() == 0,
                input_components == crate::image::typed_components_output_view(crate::image::typed_image_components(&decoded)),
                input_components == Seq::new(crate::image::typed_image_value_view(decoded).1.len(),
                    |i: int| (crate::image::typed_image_value_view(decoded).1[i], crate::image::typed_image_value_view(decoded).2[i])),
                crate::image::typed_components_output_view(copied@) == input_components.take(component_index as int),
                decreases component_count - component_index,
            )
        )]
        while component_index < component_count {
            let component = copy_typed_component(
                decoded
                    .components()
                    .get(component_index)
                    .ok_or_else(invalid_jp2_output)?,
            )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_typed_components_output_push(copied@, component);
                assert(input_components.take(component_index as int + 1) =~= input_components.take(component_index as int).push(input_components[component_index as int]));
            }
            copied.push(component);
            component_index = component_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::image::typed_components_output_view(copied@) =~= input_components);
        }
        copied
    } else {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_output_mapping_empty(input_components, raw_header);
        }
        let mut mapped = Vec::with_capacity(header.component_mappings.len());
        #[cfg(verus_keep_ghost)]
        proof! { assert(crate::image::typed_components_output_view(mapped@) =~= Seq::empty()); }
        let mut mapping_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant mapping_index <= header.component_mappings.len(),
                raw_header == jp2::output_header_view(header),
                raw_header.1.len() > 0,
                input_components == crate::image::typed_components_output_view(crate::image::typed_image_components(&decoded)),
                input_components == Seq::new(crate::image::typed_image_value_view(decoded).1.len(),
                    |i: int| (crate::image::typed_image_value_view(decoded).1[i], crate::image::typed_image_value_view(decoded).2[i])),
                crate::specs::part2_output_mapping_prefix(input_components, raw_header, mapping_index as nat)
                    == Ok(crate::image::typed_components_output_view(mapped@)),
                decreases header.component_mappings.len() - mapping_index,
            )
        )]
        while mapping_index < header.component_mappings.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_output_mapping_step(input_components, raw_header, mapping_index as nat);
                crate::proofs::production_impl::production_output_mapping_error(input_components, raw_header, mapping_index as nat + 1, raw_header.1.len());
            }
            let mapping = header
                .component_mappings
                .get(mapping_index)
                .ok_or_else(invalid_jp2_output)?;
            let source = decoded.component(mapping.component)?;
            let component = match mapping.mapping_type {
                jp2::MappingType::Direct => copy_typed_component(source)?,
                jp2::MappingType::Palette { column } => {
                    let palette = header.palette.as_ref().ok_or_else(invalid_jp2_output)?;
                    map_palette_component(source, palette, column)?
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_typed_components_output_push(mapped@, component);
            }
            mapped.push(component);
            mapping_index = mapping_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        mapped
    };

    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost mapped_start = crate::image::typed_components_output_view(components@); }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_output_definition_empty(mapped_start, raw_header.2);
    }
    let mut definition_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant definition_index <= header.channel_definition_records.len(),
            raw_header == jp2::output_header_view(header),
            input_components == crate::image::typed_components_output_view(crate::image::typed_image_components(&decoded)),
            input_components == Seq::new(crate::image::typed_image_value_view(decoded).1.len(),
                |i: int| (crate::image::typed_image_value_view(decoded).1[i], crate::image::typed_image_value_view(decoded).2[i])),
            (if raw_header.1.len() == 0 { Ok(input_components) }
                else { crate::specs::part2_output_mapping_prefix(input_components, raw_header, raw_header.1.len()) })
                == Ok(mapped_start),
            crate::specs::part2_output_definition_prefix(mapped_start, raw_header.2, definition_index as nat)
                == Ok(crate::image::typed_components_output_view(components@)),
            decreases header.channel_definition_records.len() - definition_index,
        )
    )]
    while definition_index < header.channel_definition_records.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous_components = crate::image::typed_components_output_view(components@); }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_output_definition_step(mapped_start, raw_header.2, definition_index as nat);
            crate::proofs::production_impl::production_output_definition_error(mapped_start, raw_header.2, definition_index as nat + 1, raw_header.2.len());
        }
        let record = header
            .channel_definition_records
            .get(definition_index)
            .ok_or_else(invalid_jp2_output)?;
        let component = components
            .get_mut(usize::from(record.channel))
            .ok_or_else(invalid_jp2_output)?;
        component.add_channel_definition(record.definition);
        #[cfg(verus_keep_ghost)]
        proof! {
            let channel = record.channel as int;
            let previous = previous_components[channel];
            let current = crate::image::typed_component_output_view(&components@[channel]);
            assert(current.0 == previous.0);
            assert(current.1 =~= previous.1.push(crate::image::channel_definition_view(record.definition)));
            assert(crate::image::typed_components_output_view(components@) =~= previous_components.update(
                channel, (previous.0, previous.1.push(crate::image::channel_definition_view(record.definition)))));
        }
        definition_index = definition_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    crate::image::typed_image_from_components_with_origin(
        decoded.width(),
        decoded.height(),
        decoded.x_origin(),
        decoded.y_origin(),
        components,
        limits,
    )
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::image::typed_component_output(result)
            == crate::specs::part2_typed_component_copy(crate::image::typed_component_output_view(source)),
    )
)]
pub(super) fn copy_typed_component(source: &TypedComponent) -> Result<TypedComponent, DecodeError> {
    let samples = match source.samples() {
        TypedSamples::Signed(source_samples) => {
            let mut copied = Vec::with_capacity(source_samples.len());
            let mut index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant index <= source_samples.len(),
                    copied@ == source_samples@.take(index as int),
                    decreases source_samples.len() - index,
                )
            )]
            while index < source_samples.len() {
                copied.push(*source_samples.get(index).ok_or_else(invalid_jp2_output)?);
                index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! { assert(copied@ =~= source_samples@); }
            TypedSamples::Signed(copied)
        }
        TypedSamples::Unsigned(source_samples) => {
            let mut copied = Vec::with_capacity(source_samples.len());
            let mut index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant index <= source_samples.len(),
                    copied@ == source_samples@.take(index as int),
                    decreases source_samples.len() - index,
                )
            )]
            while index < source_samples.len() {
                copied.push(*source_samples.get(index).ok_or_else(invalid_jp2_output)?);
                index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! { assert(copied@ =~= source_samples@); }
            TypedSamples::Unsigned(copied)
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::image::typed_samples_view(&samples) == crate::image::typed_component_view(source).samples);
    }
    let mut copied = crate::image::typed_component_from_parts(
        source.width(),
        source.height(),
        source.info(),
        samples,
    );
    let definition_count = source.channel_definitions().len();
    let mut definition_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant definition_index <= definition_count,
            definition_count == crate::image::typed_component_definitions(source).len(),
            crate::image::typed_component_view(&copied) == crate::image::typed_component_view(source),
            crate::image::typed_component_definitions(&copied)
                == crate::image::typed_component_definitions(source).take(definition_index as int),
            decreases definition_count - definition_index,
        )
    )]
    while definition_index < definition_count {
        copied.add_channel_definition(
            *source
                .channel_definitions()
                .get(definition_index)
                .ok_or_else(invalid_jp2_output)?,
        );
        definition_index = definition_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::image::typed_component_definitions(&copied)
            =~= crate::image::typed_component_definitions(source));
    }
    Ok(copied)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::image::typed_component_output(result) == crate::specs::part2_palette_component(
            crate::image::typed_component_view(source), crate::jp2::palette_view(palette), column,
        ),
    )
)]
pub(super) fn map_palette_component(
    source: &TypedComponent,
    palette: &jp2::Palette,
    column: u8,
) -> Result<TypedComponent, DecodeError> {
    let descriptor = palette
        .columns()
        .get(usize::from(column))
        .ok_or_else(invalid_jp2_output)?;
    let precision = descriptor.precision;
    if precision == 0 || precision > 38 {
        return Err(invalid_jp2_output());
    }
    let sample_count = match source.samples() {
        TypedSamples::Signed(samples) => samples.len(),
        TypedSamples::Unsigned(samples) => samples.len(),
    };
    let mut signed_samples = if descriptor.signed {
        Vec::with_capacity(sample_count)
    } else {
        Vec::new()
    };
    let mut unsigned_samples = if descriptor.signed {
        Vec::new()
    } else {
        Vec::with_capacity(sample_count)
    };
    let mut sample_index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_palette_samples_empty(
            crate::image::typed_component_view(source).samples, crate::jp2::palette_view(palette), column,
        );
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant sample_index <= sample_count,
            sample_count as nat == crate::specs::part2_typed_sample_count(crate::image::typed_component_view(source).samples),
            column < crate::jp2::palette_view(palette).1.len(),
            *descriptor == crate::jp2::palette_view(palette).1[column as int],
            precision == descriptor.precision, 0 < precision <= 38,
            crate::specs::part2_palette_samples(
                crate::image::typed_component_view(source).samples, crate::jp2::palette_view(palette), column, sample_index as nat,
            ) == Ok(if descriptor.signed {
                crate::specs::Part1TypedSampleSequence::Signed(signed_samples@)
            } else { crate::specs::Part1TypedSampleSequence::Unsigned(unsigned_samples@) }),
            decreases sample_count - sample_index,
        )
    )]
    while sample_index < sample_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_palette_samples_step(
                crate::image::typed_component_view(source).samples, crate::jp2::palette_view(palette), column, sample_index as nat,
            );
        }
        let index_status = match source.samples() {
            TypedSamples::Signed(samples) => {
                let value = *samples.get(sample_index).ok_or_else(invalid_jp2_output)?;
                u16::try_from(value)
            }
            TypedSamples::Unsigned(samples) => {
                let value = *samples.get(sample_index).ok_or_else(invalid_jp2_output)?;
                u16::try_from(value)
            }
        };
        let palette_index = match index_status {
            Ok(index) => index,
            Err(_) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_palette_sample_error(
                        crate::image::typed_component_view(source), crate::jp2::palette_view(palette),
                        column, sample_index, crate::specs::part2_color_input_error(),
                    );
                }
                return Err(invalid_jp2_output());
            }
        };
        if palette_index >= palette.entries() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_palette_sample_error(
                    crate::image::typed_component_view(source), crate::jp2::palette_view(palette),
                    column, sample_index, crate::specs::part2_color_input_error(),
                );
            }
            return Err(invalid_jp2_output());
        }
        let value_status = palette.value(palette_index, column);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = value_status {
                crate::proofs::production_impl::production_palette_sample_error(
                    crate::image::typed_component_view(source), crate::jp2::palette_view(palette),
                    column, sample_index, error,
                );
            }
        }
        let value = value_status?;
        if descriptor.signed {
            let modulus = palette_modulus(precision)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(2 <= modulus <= 274877906944) by(bit_vector)
                    requires 0 < precision <= 38, modulus == 1u64 << precision;
            }
            let half = i64::try_from(modulus.checked_div(2).ok_or_else(arithmetic_overflow)?)
                .map_err(|_| arithmetic_overflow())?;
            let minimum = 0_i64.checked_sub(half).ok_or_else(arithmetic_overflow)?;
            let maximum = half.checked_sub(1).ok_or_else(arithmetic_overflow)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(half == 1i64 << ((precision - 1) as u8)) by(bit_vector)
                    requires 0 < precision <= 38, modulus == 1u64 << precision,
                        half >= 0, half as u64 == modulus / 2;
            }
            if value < minimum || value > maximum {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_palette_sample_error(
                        crate::image::typed_component_view(source), crate::jp2::palette_view(palette),
                        column, sample_index, crate::specs::part2_color_input_error(),
                    );
                }
                return Err(invalid_jp2_output());
            }
            signed_samples.push(value);
        } else {
            let modulus = palette_modulus(precision)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(2 <= modulus <= 274877906944) by(bit_vector)
                    requires 0 < precision <= 38, modulus == 1u64 << precision;
            }
            let maximum = modulus.checked_sub(1).ok_or_else(arithmetic_overflow)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(maximum < 274877906944) by(bit_vector)
                    requires 0 < precision <= 38, maximum == (1u64 << precision) - 1;
                assert(maximum as i64 == ((1i64 << precision) - 1)) by(bit_vector)
                    requires 0 < precision <= 38, maximum == (1u64 << precision) - 1;
            }
            let unsigned_value = match u64::try_from(value) {
                Ok(value) => value,
                Err(_) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_palette_sample_error(
                            crate::image::typed_component_view(source), crate::jp2::palette_view(palette),
                            column, sample_index, crate::specs::part2_color_input_error(),
                        );
                    }
                    return Err(invalid_jp2_output());
                }
            };
            if unsigned_value > maximum {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_palette_sample_error(
                        crate::image::typed_component_view(source), crate::jp2::palette_view(palette),
                        column, sample_index, crate::specs::part2_color_input_error(),
                    );
                }
                return Err(invalid_jp2_output());
            }
            unsigned_samples.push(unsigned_value);
        }
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    let mut info = source.info();
    info.precision = descriptor.precision;
    info.signed = descriptor.signed;
    let samples = if descriptor.signed {
        TypedSamples::Signed(signed_samples)
    } else {
        TypedSamples::Unsigned(unsigned_samples)
    };
    Ok(crate::image::typed_component_from_parts(
        source.width(),
        source.height(),
        info,
        samples,
    ))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::part2_palette_modulus(precision),)
)]
pub(super) fn palette_modulus(precision: u8) -> Result<u64, DecodeError> {
    if precision == 0 || precision > 38 {
        return Err(invalid_jp2_output());
    }
    let mut modulus = 1_u64;
    let mut bit = 0_u8;
    #[cfg(verus_keep_ghost)]
    proof! { assert(1u64 << 0u32 == 1) by(bit_vector); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant bit <= precision, 0 < precision <= 38,
            modulus == 1u64 << (bit as u32),
            decreases precision - bit,
        )
    )]
    while bit < precision {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(modulus <= 137438953472) by(bit_vector)
                requires bit < 38, modulus == 1u64 << (bit as u32);
            assert(modulus * 2 == 1u64 << ((bit + 1) as u32)) by(bit_vector)
                requires bit < 38, modulus == 1u64 << (bit as u32);
        }
        modulus = modulus.checked_mul(2).ok_or_else(arithmetic_overflow)?;
        bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(modulus)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(error => ensures error == crate::specs::part2_color_input_error(),)
)]
pub(super) fn invalid_jp2_output() -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ContainerCodestreamMismatch,
    }
}
