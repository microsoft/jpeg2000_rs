//! Container and associated codestream headers, image dimensions, and bit depths.

use super::{
    BoxRef, BoxType, ChannelDefinitionRecord, ChannelType, ColorMethod, ColorSpecification,
    ComponentBitDepth, DecodeError, ImageHeader, Jp2Header, MalformedKind, Resource,
    ResourceLimits, add_offset, box_reader_from_input, parse_channel_definition,
    parse_color_specification, parse_component_mapping, parse_palette, parse_resolution_superbox,
    read_u16, read_u32, rebase_error, required_box, validate_color_specification_prefix,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_codestream_header_storage_result(
        payload@,super::raw_header_option(defaults),*limits,base_offset,super::raw_jp2_header_outcome(result)),
    super::raw_jp2_header_outcome(result) != Err(DecodeError::AllocationFailed) ==>
        super::raw_jp2_header_outcome(result) == crate::specs::part2_parse_codestream_header(
        payload@, super::raw_header_option(defaults), *limits, base_offset),
))]
pub(super) fn parse_codestream_header(
    payload: &[u8],
    defaults: Option<&Jp2Header>,
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<Jp2Header, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_codestream_header_storage_normal(payload@,super::raw_header_option(defaults),*limits,base_offset); }
    let first = parse_jp2_header(payload, limits, base_offset);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost first_value=super::raw_jp2_header_outcome(first); }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_codestream_header_storage_first(payload@,super::raw_header_option(defaults),*limits,base_offset,first_value); }
    match first {
        Ok(header) => return Ok(header),
        Err(DecodeError::AllocationFailed) => return Err(DecodeError::AllocationFailed),
        Err(_) => {}
    }
    let default_header = defaults.ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_raw_header_missing(base_offset),
        ))]
        || DecodeError::malformed(base_offset, MalformedKind::MissingRequiredStructure),
    )?;
    let copied = super::clone_support::try_jp2_header_clone(default_header);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=super::raw_jp2_header_outcome(copied) {
            crate::specs::part2_codestream_header_storage_clone_error(payload@,super::raw_header_option(defaults),
                *limits,base_offset,first_value,super::raw_jp2_header_view(default_header),error);
        }
    }
    let mut header = copied?;
    let mut reader = box_reader_from_input(payload, limits)?;
    let mut image_override = false;
    let mut color_override = false;
    let mut saw_bpcc = false;
    let mut palette_override = false;
    let mut mapping_override = false;
    let mut definition_override = false;
    let mut resolution_override = false;
    let mut nested_box_count = 0_u32;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_parse_codestream_header(
    payload@, super::raw_header_option(defaults), *limits, base_offset); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost mut storage_prefix=crate::specs::part2_codestream_header_storage_prefix(
            payload@,super::raw_header_option(defaults),*limits,base_offset,first_value,super::box_reader_state(&reader),
            super::associated_header_state(&header,image_override,color_override,saw_bpcc,palette_override,mapping_override,
                definition_override,resolution_override,nested_box_count));
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant_except_break expected == crate::specs::part2_associated_header_boxes(
                payload@, super::box_reader_state(&reader),
                super::associated_header_state(&header, image_override, color_override, saw_bpcc,
                    palette_override, mapping_override, definition_override, resolution_override, nested_box_count),
                *limits, base_offset),
                expected == crate::specs::part2_parse_codestream_header(
                    payload@, super::raw_header_option(defaults), *limits, base_offset),
                crate::specs::part2_codestream_header_storage_result(payload@,super::raw_header_option(defaults),*limits,base_offset,expected),
                crate::specs::part2_codestream_header_storage_at(payload@,super::raw_header_option(defaults),*limits,base_offset,
                    super::box_reader_state(&reader),
                    super::associated_header_state(&header,image_override,color_override,saw_bpcc,palette_override,mapping_override,
                        definition_override,resolution_override,nested_box_count),storage_prefix),
            ensures expected == crate::specs::part2_associated_header_finish(
                super::associated_header_state(&header, image_override, color_override, saw_bpcc,
                    palette_override, mapping_override, definition_override, resolution_override, nested_box_count), base_offset),
                crate::specs::part2_codestream_header_storage_result(payload@,super::raw_header_option(defaults),*limits,base_offset,expected),
            decreases payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_associated_header_boxes); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_reader=super::box_reader_state(&reader);
            let ghost previous_state=super::associated_header_state(&header,image_override,color_override,saw_bpcc,palette_override,
                mapping_override,definition_override,resolution_override,nested_box_count);
        }
        let previous_position = reader.position;
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if reader.position <= previous_position || reader.position > payload.len() {
            return Err(DecodeError::malformed(
                add_offset(base_offset, previous_position as u64)?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let box_ref = next.map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
            ))]
            |error| rebase_error(error, base_offset),
        )?;
        nested_box_count = nested_box_count.checked_add(1).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
            ))]
            || DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
        )?;
        let stepped = parse_codestream_header_box(
            box_ref,
            &mut header,
            &mut image_override,
            &mut color_override,
            &mut saw_bpcc,
            &mut palette_override,
            &mut mapping_override,
            &mut definition_override,
            &mut resolution_override,
            nested_box_count,
            limits,
            base_offset,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=stepped{
                if error==DecodeError::AllocationFailed{
                    crate::specs::part2_codestream_header_storage_box_error(payload@,super::raw_header_option(defaults),*limits,base_offset,
                        storage_prefix,previous_reader,previous_state,super::box_reference_view(box_ref),error);
                }
            }
        }
        stepped?;
        #[cfg(verus_keep_ghost)]
        proof! {
            storage_prefix=crate::specs::part2_codestream_header_storage_advance(payload@,super::raw_header_option(defaults),*limits,base_offset,
                storage_prefix,previous_reader,previous_state,super::box_reference_view(box_ref),
                super::associated_header_state(&header,image_override,color_override,saw_bpcc,palette_override,
                    mapping_override,definition_override,resolution_override,nested_box_count));
        }
    }
    if image_override && matches!(header.image.bit_depth, ComponentBitDepth::Variable) != saw_bpcc {
        return Err(DecodeError::malformed(
            base_offset,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    if header.palette.is_some() && header.component_mappings.is_empty() {
        return Err(DecodeError::malformed(
            base_offset,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    header.nested_box_count = nested_box_count;
    Ok(header)
}

#[allow(
    clippy::too_many_arguments,
    reason = "One checked box preserves the existing independent override owners"
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_associated_header_box_storage_result(super::box_reference_view(box_ref),
        super::associated_header_state(old(header),*old(image_override),*old(color_override),*old(saw_bpcc),
            *old(palette_override),*old(mapping_override),*old(definition_override),*old(resolution_override),_nested_box_count),
        *limits,base_offset,crate::specs::part2_associated_header_box_outcome(result,
            super::associated_header_state(final(header),*final(image_override),*final(color_override),*final(saw_bpcc),
                *final(palette_override),*final(mapping_override),*final(definition_override),*final(resolution_override),_nested_box_count))),
    result != Err(DecodeError::AllocationFailed) ==>
        crate::specs::part2_associated_header_box_outcome(result,
            super::associated_header_state(final(header),*final(image_override),*final(color_override),*final(saw_bpcc),
                *final(palette_override),*final(mapping_override),*final(definition_override),*final(resolution_override),_nested_box_count))
        == crate::specs::part2_associated_header_step(super::box_reference_view(box_ref),
            super::associated_header_state(old(header),*old(image_override),*old(color_override),*old(saw_bpcc),
                *old(palette_override),*old(mapping_override),*old(definition_override),*old(resolution_override),_nested_box_count),
            *limits,base_offset),
))]
fn parse_codestream_header_box(
    box_ref: BoxRef<'_>,
    header: &mut Jp2Header,
    image_override: &mut bool,
    color_override: &mut bool,
    saw_bpcc: &mut bool,
    palette_override: &mut bool,
    mapping_override: &mut bool,
    definition_override: &mut bool,
    resolution_override: &mut bool,
    _nested_box_count: u32,
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before=super::associated_header_state(header,*image_override,*color_override,*saw_bpcc,*palette_override,
            *mapping_override,*definition_override,*resolution_override,_nested_box_count);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_associated_header_box_storage_normal(super::box_reference_view(box_ref),before,*limits,base_offset);
        reveal(crate::specs::part2_associated_header_step);
    }
    let box_type = box_ref.header.box_type();
    if box_type.equals(BoxType::IMAGE_HEADER) {
        if *image_override {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxOrder,
            ));
        }
        header.image = parse_image_header(box_ref, limits, base_offset)?;
        header.palette = None;
        header.component_mappings.clear();
        header.channel_definition_records.clear();
        header.palette_entries = 0;
        header.palette_columns = 0;
        header.component_mapping_entries = 0;
        header.channel_definitions = 0;
        *image_override = true;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(header.component_mappings@ =~= Seq::<super::ComponentMapping>::empty());
            assert(super::channel_definition_records_view(header.channel_definition_records@)
                =~= Seq::<crate::specs::Part2ChannelRecord>::empty());
        }
    } else if box_type.equals(BoxType::BITS_PER_COMPONENT) {
        if *saw_bpcc {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxOrder,
            ));
        }
        validate_bpcc(box_ref, header.image, base_offset)?;
        *saw_bpcc = true;
    } else if box_type.equals(BoxType::COLOR_SPECIFICATION) {
        if crate::refinement::first_override_allowed(*color_override) {
            header.color = parse_color_specification(box_ref, base_offset)?;
            *color_override = true;
        } else {
            validate_color_specification_prefix(box_ref, base_offset)?;
        }
    } else if box_type.equals(BoxType::PALETTE) {
        if *palette_override || *mapping_override || *definition_override {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxOrder,
            ));
        }
        let palette = parse_palette(box_ref, base_offset)?;
        header.palette_entries = palette.entries;
        header.palette_columns = u8::try_from(palette.columns.len()).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                ))]
            |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
        )?;
        header.palette = Some(palette);
        *palette_override = true;
    } else if box_type.equals(BoxType::COMPONENT_MAPPING) {
        if *mapping_override || *definition_override {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxOrder,
            ));
        }
        let palette_columns = match &header.palette {
            Some(palette) => u8::try_from(palette.columns.len()).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                    ))]
                |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
            )?,
            None => 0,
        };
        header.component_mappings = parse_component_mapping(
            box_ref,
            header.image.components,
            palette_columns,
            limits,
            base_offset,
        )?;
        header.component_mapping_entries = u16::try_from(header.component_mappings.len()).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                ))]
            |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
        )?;
        *mapping_override = true;
    } else if box_type.equals(BoxType::CHANNEL_DEFINITION) {
        if *definition_override {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxOrder,
            ));
        }
        let output_channels = if header.component_mappings.is_empty() {
            header.image.components
        } else {
            u16::try_from(header.component_mappings.len()).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                    ))]
                |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
            )?
        };
        let parsed = parse_channel_definition(box_ref, output_channels, base_offset);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=parsed {
                if error==DecodeError::AllocationFailed {
                    crate::specs::part2_associated_header_box_storage_error(
                        super::box_reference_view(box_ref),before,*limits,base_offset,output_channels,error);
                }
            }
        }
        header.channel_definition_records = parsed?;
        header.channel_definitions = u16::try_from(header.channel_definition_records.len())
            .map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                ))]
                |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
            )?;
        *definition_override = true;
    } else if box_type.equals(BoxType::RESOLUTION) {
        if *resolution_override {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxOrder,
            ));
        }
        let (capture, display) = parse_resolution_superbox(
            box_ref.payload,
            limits,
            add_offset(base_offset, box_ref.header.payload_offset()?)?,
        )?;
        header.capture_resolution = capture;
        header.display_resolution = display;
        *resolution_override = true;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_jp2_header_storage_result(payload@,*limits,base_offset,false,super::raw_jp2_header_outcome(result)),
    super::raw_jp2_header_outcome(result) != Err(DecodeError::AllocationFailed) ==>
        super::raw_jp2_header_outcome(result) == crate::specs::part2_parse_jp2_header(payload@, *limits, base_offset),
))]
pub(super) fn parse_jp2_header(
    payload: &[u8],
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<Jp2Header, DecodeError> {
    parse_jp2_header_profile(payload, limits, base_offset, false)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::color_specification_outcome(result)
        == crate::specs::part2_unspecified_jph_color(
            super::channel_definition_records_view(definitions@), base_offset),
))]
pub(super) fn unspecified_jph_color(
    definitions: &[ChannelDefinitionRecord],
    base_offset: u64,
) -> Result<ColorSpecification, DecodeError> {
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= definitions.len(),
                forall |i: int| 0 <= i < index ==>
                    crate::image::channel_definition_view(definitions@[i].definition).0 != ChannelType::Color,
            decreases definitions.len() - index,
        )
    )]
    while index < definitions.len() {
        if matches!(
            definitions[index].definition.channel_type(),
            ChannelType::Color
        ) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(super::channel_definition_records_view(definitions@)[index as int].1.0
                    == ChannelType::Color);
                assert(exists |i: int| 0 <= i < definitions.len()
                    && super::channel_definition_records_view(definitions@)[i].1.0 == ChannelType::Color);
            }
            return Err(DecodeError::malformed(
                base_offset,
                MalformedKind::InvalidProfile,
            ));
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(super::full_color_specification_view); }
    Ok(ColorSpecification {
        method: ColorMethod::Unspecified,
        precedence: 0,
        approximation: 0,
        icc_profile: None,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_jp2_header_storage_result(payload@,*limits,base_offset,allow_unspecified,super::raw_jp2_header_outcome(result)),
    super::raw_jp2_header_outcome(result) != Err(DecodeError::AllocationFailed) ==>
        super::raw_jp2_header_outcome(result) == crate::specs::part2_parse_jp2_header_profile(
        payload@, *limits, base_offset, allow_unspecified),
))]
pub(super) fn parse_jp2_header_profile(
    payload: &[u8],
    limits: &ResourceLimits,
    base_offset: u64,
    allow_unspecified: bool,
) -> Result<Jp2Header, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_jp2_header_storage_normal(payload@,*limits,base_offset,allow_unspecified); }
    let mut reader = box_reader_from_input(payload, limits)?;
    let image_box = required_box(&mut reader, 0).map_err(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
        ))]
        |error| rebase_error(error, base_offset),
    )?;
    if !image_box.header.box_type().equals(BoxType::IMAGE_HEADER) {
        return Err(DecodeError::malformed(
            add_offset(base_offset, image_box.header.offset())?,
            MalformedKind::InvalidBoxOrder,
        ));
    }
    let image = parse_image_header(image_box, limits, base_offset)?;
    let mut color = None;
    let mut saw_bpcc = false;
    let mut palette = None;
    let mut component_mappings = Vec::new();
    let mut channel_definition_records = Vec::new();
    let mut capture_resolution = None;
    let mut display_resolution = None;
    let mut nested_box_count = 1_u32;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_parse_jp2_header_profile(payload@, *limits, base_offset, allow_unspecified); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost machine=crate::specs::part2_main_header_storage_machine(payload@,*limits,base_offset,allow_unspecified);
        let ghost root=|events:Seq<crate::specs::Part2JpipSnapshotEvent>|crate::specs::part2_jp2_header_storage_run(payload@,*limits,base_offset,allow_unspecified,events);
        let ghost mut storage_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(component_mappings@ =~= Seq::<super::ComponentMapping>::empty());
        assert(super::channel_definition_records_view(channel_definition_records@) =~= Seq::<crate::specs::Part2ChannelRecord>::empty());
        crate::specs::part2_header_storage_machines_valid(payload@,*limits,base_offset,allow_unspecified);
        assert forall|tail:Seq<crate::specs::Part2JpipSnapshotEvent>|root(storage_prefix+tail)
            ==crate::specs::part2_header_storage_boxes_run(machine,super::box_reader_state(&reader),
                super::raw_header_state(image,&color,saw_bpcc,&palette,component_mappings@,channel_definition_records@,
                    capture_resolution,display_resolution,nested_box_count),tail) by { assert(storage_prefix+tail =~= tail); }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant_except_break expected == crate::specs::part2_raw_header_boxes(
                payload@, super::box_reader_state(&reader),
                super::raw_header_state(image, &color, saw_bpcc, &palette, component_mappings@,
                    channel_definition_records@, capture_resolution, display_resolution, nested_box_count),
                *limits, base_offset, allow_unspecified),
                expected == crate::specs::part2_parse_jp2_header_profile(payload@, *limits, base_offset, allow_unspecified),
                crate::specs::part2_jp2_header_storage_result(payload@,*limits,base_offset,allow_unspecified,expected),
                machine==crate::specs::part2_main_header_storage_machine(payload@,*limits,base_offset,allow_unspecified),
                root==(|events:Seq<crate::specs::Part2JpipSnapshotEvent>|crate::specs::part2_jp2_header_storage_run(payload@,*limits,base_offset,allow_unspecified,events)),
                crate::specs::part2_header_storage_machine_valid(machine),
                crate::specs::part2_cold_phase(root,storage_prefix,|events|crate::specs::part2_header_storage_boxes_run(
                    machine,super::box_reader_state(&reader),
                    super::raw_header_state(image,&color,saw_bpcc,&palette,component_mappings@,channel_definition_records@,
                        capture_resolution,display_resolution,nested_box_count),events)),
            ensures expected == crate::specs::part2_raw_header_finish(
                super::raw_header_state(image, &color, saw_bpcc, &palette, component_mappings@,
                    channel_definition_records@, capture_resolution, display_resolution, nested_box_count), base_offset, allow_unspecified),
                crate::specs::part2_jp2_header_storage_result(payload@,*limits,base_offset,allow_unspecified,expected),
            decreases payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_raw_header_boxes); reveal(crate::specs::part2_raw_header_step); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_reader=super::box_reader_state(&reader);
            let ghost previous_state=super::raw_header_state(image,&color,saw_bpcc,&palette,component_mappings@,
                channel_definition_records@,capture_resolution,display_resolution,nested_box_count);
        }
        let previous_position = reader.position;
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if reader.position <= previous_position || reader.position > payload.len() {
            return Err(DecodeError::malformed(
                add_offset(base_offset, previous_position as u64)?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let box_ref = next.map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
            ))]
            |error| rebase_error(error, base_offset),
        )?;
        nested_box_count = nested_box_count.checked_add(1).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
            ))]
            || DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
        )?;
        let box_type = box_ref.header.box_type();
        if box_type.equals(BoxType::IMAGE_HEADER) {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxOrder,
            ));
        }
        if box_type.equals(BoxType::BITS_PER_COMPONENT) {
            if saw_bpcc {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            validate_bpcc(box_ref, image, base_offset)?;
            saw_bpcc = true;
        } else if box_type.equals(BoxType::COLOR_SPECIFICATION) {
            if color.is_none() {
                color = Some(parse_color_specification(box_ref, base_offset)?);
            } else {
                validate_color_specification_prefix(box_ref, base_offset)?;
            }
        } else if box_type.equals(BoxType::PALETTE) {
            if palette.is_some() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            palette = Some(parse_palette(box_ref, base_offset)?);
        } else if box_type.equals(BoxType::COMPONENT_MAPPING) {
            if !component_mappings.is_empty() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let palette_columns = match &palette {
                Some(parsed) => u8::try_from(parsed.columns.len()).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                    ))]
                    |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
                )?,
                None => 0,
            };
            component_mappings = parse_component_mapping(
                box_ref,
                image.components,
                palette_columns,
                limits,
                base_offset,
            )?;
        } else if box_type.equals(BoxType::CHANNEL_DEFINITION) {
            if !channel_definition_records.is_empty() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let output_channels = if component_mappings.is_empty() {
                image.components
            } else {
                u16::try_from(component_mappings.len()).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                    ))]
                    |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
                )?
            };
            let parsed = parse_channel_definition(box_ref, output_channels, base_offset);
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=parsed {
                    if error==DecodeError::AllocationFailed {
                        crate::specs::part2_header_storage_root_error(root,storage_prefix,machine,previous_reader,previous_state,
                            super::box_reference_view(box_ref),crate::specs::Part2ChannelStorageContext {
                                input:super::box_reference_view(box_ref),channels:output_channels,base:base_offset},error);
                        crate::specs::part2_jp2_header_storage_observed(payload@,*limits,base_offset,allow_unspecified,Err(error));
                    }
                }
            }
            channel_definition_records = parsed?;
        } else if box_type.equals(BoxType::RESOLUTION) {
            let (capture, display) = parse_resolution_superbox(
                box_ref.payload,
                limits,
                add_offset(base_offset, box_ref.header.payload_offset()?)?,
            )?;
            if capture_resolution.is_some() || display_resolution.is_some() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            capture_resolution = capture;
            display_resolution = display;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            storage_prefix=crate::specs::part2_header_storage_root_advance(root,storage_prefix,machine,previous_reader,previous_state,
                super::box_reference_view(box_ref),super::raw_header_state(image,&color,saw_bpcc,&palette,component_mappings@,
                    channel_definition_records@,capture_resolution,display_resolution,nested_box_count));
        }
    }

    if matches!(image.bit_depth, ComponentBitDepth::Variable) != saw_bpcc {
        return Err(DecodeError::malformed(
            base_offset,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    if palette.is_some() && component_mappings.is_empty() {
        return Err(DecodeError::malformed(
            base_offset,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    let color = match color {
        Some(color) => color,
        None if allow_unspecified && image.unknown_color_space => {
            unspecified_jph_color(&channel_definition_records, base_offset)?
        }
        None => {
            return Err(DecodeError::malformed(
                base_offset,
                MalformedKind::MissingRequiredStructure,
            ));
        }
    };

    let (palette_entries, palette_columns) = match &palette {
        Some(parsed) => (parsed.entries(), parsed.columns.len() as u8),
        None => (0, 0),
    };
    let component_mapping_entries = u16::try_from(component_mappings.len()).map_err(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
        ))]
        |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
    )?;
    let channel_definitions = u16::try_from(channel_definition_records.len()).map_err(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
        ))]
        |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
    )?;
    Ok(Jp2Header {
        image,
        color,
        nested_box_count,
        palette_entries,
        palette_columns,
        component_mapping_entries,
        channel_definitions,
        palette,
        component_mappings,
        channel_definition_records,
        capture_resolution,
        display_resolution,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_parse_image_header(super::box_reference_view(box_ref), limits, base_offset),
))]
pub(super) fn parse_image_header(
    box_ref: BoxRef<'_>,
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<ImageHeader, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_parse_image_header); }
    if box_ref.payload.len() != 14 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let height = read_u32([
        box_ref.payload[0],
        box_ref.payload[1],
        box_ref.payload[2],
        box_ref.payload[3],
    ]);
    let width = read_u32([
        box_ref.payload[4],
        box_ref.payload[5],
        box_ref.payload[6],
        box_ref.payload[7],
    ]);
    let components = read_u16([box_ref.payload[8], box_ref.payload[9]]);
    if width == 0 || height == 0 || components == 0 || box_ref.payload[11] != 7 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxContents,
        ));
    }
    if width > limits.maximum_width() {
        return Err(DecodeError::limit(
            Resource::Width,
            u64::from(limits.maximum_width()),
            u64::from(width),
        ));
    }
    if height > limits.maximum_height() {
        return Err(DecodeError::limit(
            Resource::Height,
            u64::from(limits.maximum_height()),
            u64::from(height),
        ));
    }
    if components > limits.maximum_components() {
        return Err(DecodeError::limit(
            Resource::Components,
            u64::from(limits.maximum_components()),
            u64::from(components),
        ));
    }
    let pixels = u64::from(width)
        .checked_mul(u64::from(height))
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset: base_offset, kind: MalformedKind::ArithmeticOverflow }),
            ))]
            || DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
        )?;
    if pixels > limits.maximum_pixels() {
        return Err(DecodeError::limit(
            Resource::Pixels,
            limits.maximum_pixels(),
            pixels,
        ));
    }
    let bit_depth = parse_bit_depth(box_ref.payload[10], base_offset)?;
    let unknown_color_space = match box_ref.payload[12] {
        0 => false,
        1 => true,
        _ => {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
    };
    let intellectual_property = match box_ref.payload[13] {
        0 => false,
        1 => true,
        _ => {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
    };
    Ok(ImageHeader {
        width,
        height,
        components,
        bit_depth,
        unknown_color_space,
        intellectual_property,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_container_bit_depth(value, offset),
))]
pub(super) fn parse_bit_depth(value: u8, offset: u64) -> Result<ComponentBitDepth, DecodeError> {
    if value == 0xff {
        return Ok(ComponentBitDepth::Variable);
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert((value & 0x7f) <= 127u8) by(bit_vector); }
    let bits = (value & 0x7f)
        .checked_add(1)
        .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    if bits > 38 {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxContents,
        ));
    }
    Ok(ComponentBitDepth::Uniform {
        bits,
        signed: value & 0x80 != 0,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_validate_bpcc(super::box_reference_view(box_ref), image, base_offset),
))]
pub(super) fn validate_bpcc(
    box_ref: BoxRef<'_>,
    image: ImageHeader,
    base_offset: u64,
) -> Result<(), DecodeError> {
    if box_ref.payload.len() != usize::from(image.components) {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_bpcc_prefix); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= box_ref.payload.len(),
                box_ref.payload.len() == image.components,
                crate::specs::part2_bpcc_prefix(super::box_reference_view(box_ref), base_offset, index as nat) == Ok(()),
            decreases box_ref.payload.len() - index,
        )
    )]
    while index < box_ref.payload.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_bpcc_step(super::box_reference_view(box_ref), base_offset, index as nat);
            crate::specs::part2_bpcc_error(super::box_reference_view(box_ref), base_offset,
                index as nat + 1, box_ref.payload.len() as nat);
        }
        if matches!(
            parse_bit_depth(box_ref.payload[index], base_offset)?,
            ComponentBitDepth::Variable
        ) {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
        index = index.checked_add(1).ok_or_else(|| {
            DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
        })?;
    }
    Ok(())
}
