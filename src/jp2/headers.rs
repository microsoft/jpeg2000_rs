//! Container and associated codestream headers, image dimensions, and bit depths.

use super::{
    BoxRef, BoxType, ComponentBitDepth, DecodeError, ImageHeader, Jp2Header, MalformedKind,
    Resource, ResourceLimits, add_offset, box_reader_from_input, parse_channel_definition,
    parse_color_specification, parse_component_mapping, parse_palette, parse_resolution_superbox,
    read_u16, read_u32, rebase_error, required_box, validate_color_specification_prefix,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::raw_jp2_header_outcome(result) == crate::specs::part2_parse_codestream_header(
        payload@, super::raw_header_option(defaults), *limits, base_offset),
))]
pub(super) fn parse_codestream_header(
    payload: &[u8],
    defaults: Option<&Jp2Header>,
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<Jp2Header, DecodeError> {
    if let Ok(header) = parse_jp2_header(payload, limits, base_offset) {
        return Ok(header);
    }
    #[allow(
        clippy::redundant_closure,
        reason = "Checked closure exposes the full native clone contract to the pinned verifier"
    )]
    let mut header = defaults.map(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: Jp2Header =>
            ensures super::raw_jp2_header_view(&result) == super::raw_jp2_header_view(default_header),
        ))]
        |default_header| super::clone_support::jp2_header_clone(default_header),
    ).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_raw_header_missing(base_offset),
        ))]
        || DecodeError::malformed(base_offset, MalformedKind::MissingRequiredStructure),
    )?;
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
            ensures expected == crate::specs::part2_associated_header_finish(
                super::associated_header_state(&header, image_override, color_override, saw_bpcc,
                    palette_override, mapping_override, definition_override, resolution_override, nested_box_count), base_offset),
            decreases payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_associated_header_boxes); reveal(crate::specs::part2_associated_header_step); }
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
            if image_override {
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
            image_override = true;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(header.component_mappings@ =~= Seq::<super::ComponentMapping>::empty());
                assert(super::channel_definition_records_view(header.channel_definition_records@)
                    =~= Seq::<crate::specs::Part2ChannelRecord>::empty());
            }
        } else if box_type.equals(BoxType::BITS_PER_COMPONENT) {
            if saw_bpcc {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            validate_bpcc(box_ref, header.image, base_offset)?;
            saw_bpcc = true;
        } else if box_type.equals(BoxType::COLOR_SPECIFICATION) {
            if crate::refinement::first_override_allowed(color_override) {
                header.color = parse_color_specification(box_ref, base_offset)?;
                color_override = true;
            } else {
                validate_color_specification_prefix(box_ref, base_offset)?;
            }
        } else if box_type.equals(BoxType::PALETTE) {
            if palette_override || mapping_override || definition_override {
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
            palette_override = true;
        } else if box_type.equals(BoxType::COMPONENT_MAPPING) {
            if mapping_override || definition_override {
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
            header.component_mapping_entries = u16::try_from(header.component_mappings.len())
                .map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                ))]
                    |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
                )?;
            mapping_override = true;
        } else if box_type.equals(BoxType::CHANNEL_DEFINITION) {
            if definition_override {
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
            header.channel_definition_records =
                parse_channel_definition(box_ref, output_channels, base_offset)?;
            header.channel_definitions = u16::try_from(header.channel_definition_records.len())
                .map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                ))]
                    |_error| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
                )?;
            definition_override = true;
        } else if box_type.equals(BoxType::RESOLUTION) {
            if resolution_override {
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
            resolution_override = true;
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::raw_jp2_header_outcome(result) == crate::specs::part2_parse_jp2_header(payload@, *limits, base_offset),
))]
pub(super) fn parse_jp2_header(
    payload: &[u8],
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<Jp2Header, DecodeError> {
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
    proof_decl! { let ghost expected = crate::specs::part2_parse_jp2_header(payload@, *limits, base_offset); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(component_mappings@ =~= Seq::<super::ComponentMapping>::empty());
        assert(super::channel_definition_records_view(channel_definition_records@) =~= Seq::<crate::specs::Part2ChannelRecord>::empty());
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant_except_break expected == crate::specs::part2_raw_header_boxes(
                payload@, super::box_reader_state(&reader),
                super::raw_header_state(image, &color, saw_bpcc, &palette, component_mappings@,
                    channel_definition_records@, capture_resolution, display_resolution, nested_box_count),
                *limits, base_offset),
                expected == crate::specs::part2_parse_jp2_header(payload@, *limits, base_offset),
            ensures expected == crate::specs::part2_raw_header_finish(
                super::raw_header_state(image, &color, saw_bpcc, &palette, component_mappings@,
                    channel_definition_records@, capture_resolution, display_resolution, nested_box_count), base_offset),
            decreases payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_raw_header_boxes); reveal(crate::specs::part2_raw_header_step); }
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
            channel_definition_records =
                parse_channel_definition(box_ref, output_channels, base_offset)?;
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
    let color = color.ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_raw_header_missing(base_offset),
        ))]
        || DecodeError::malformed(base_offset, MalformedKind::MissingRequiredStructure),
    )?;

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
