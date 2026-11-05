//! Compositing layers, registration, opacity, and composition instructions.

use super::{
    BoxHeader, BoxReader, BoxRef, BoxType, ChannelDefinitionRecord, CodestreamRegistration,
    ColorSpecification, CompositingLayer, Composition, CompositionInstruction,
    CompositionInstructionSet, DecodeError, LayerOpacity, MalformedKind, Resource, ResourceLimits,
    add_offset, byte_at_checked, copy_bytes, inspect_metadata_box, parse_channel_definition,
    parse_color_specification, read_u16, read_u32, rebase_error,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl CompositingLayer<'_> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::box_header_offset(result) == super::source_layer_geometry(self).0,
    ))]
    pub const fn box_header(&self) -> BoxHeader {
        self.header
    }

    pub fn payload(&self) -> &[u8] {
        self.payload
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::source_layer_geometry(self).1,
    ))]
    pub const fn horizontal_grid_size(&self) -> u16 {
        self.horizontal_grid_size
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::source_layer_geometry(self).2,
    ))]
    pub const fn vertical_grid_size(&self) -> u16 {
        self.vertical_grid_size
    }

    pub fn registrations(&self) -> &[CodestreamRegistration] {
        &self.registrations
    }

    pub const fn has_color_group(&self) -> bool {
        !self.color_group.is_empty()
    }

    pub const fn has_opacity_box(&self) -> bool {
        self.opacity.is_some()
    }

    pub fn color_group(&self) -> &[ColorSpecification] {
        &self.color_group
    }

    pub fn channel_definition_records(&self) -> &[ChannelDefinitionRecord] {
        &self.channel_definition_records
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::source_opacity_reference_view(result) == super::source_layer_opacity(self),
    ))]
    pub const fn opacity(&self) -> Option<&LayerOpacity> {
        self.opacity.as_ref()
    }

    pub const fn nested_metadata_boxes(&self) -> u32 {
        self.nested_metadata_boxes
    }
}

pub(super) fn parse_compositing_layer<'a>(
    box_ref: BoxRef<'a>,
    limits: &ResourceLimits,
) -> Result<CompositingLayer<'a>, DecodeError> {
    let base_offset = box_ref.header.payload_offset()?;
    let mut reader = BoxReader::new(box_ref.payload, limits)?;
    let mut horizontal_grid_size = 1_u16;
    let mut vertical_grid_size = 1_u16;
    let mut registrations = Vec::new();
    let mut has_registration = false;
    let mut color_group = Vec::new();
    let mut channel_definition_records = Vec::new();
    let mut opacity = None;
    let mut nested_metadata_boxes = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(decreases box_ref.payload.len() as int - reader.position as int,)
    )]
    loop {
        let previous_position = reader.position;
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if reader.position <= previous_position || reader.position > box_ref.payload.len() {
            return Err(DecodeError::malformed(
                add_offset(base_offset, previous_position as u64)?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let child = next.map_err(|error| rebase_error(error, base_offset))?;
        let child_type = child.header.box_type();
        if child_type.equals(BoxType::CODESTREAM_REGISTRATION) {
            if has_registration {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let parsed = parse_codestream_registration(child, base_offset, limits)?;
            horizontal_grid_size = parsed.0;
            vertical_grid_size = parsed.1;
            registrations = parsed.2;
            has_registration = true;
        } else if child_type.equals(BoxType::COLOR_GROUP) {
            if !color_group.is_empty() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            color_group = parse_color_group(
                child,
                limits,
                add_offset(base_offset, child.header.payload_offset()?)?,
            )?;
        } else if child_type.equals(BoxType::OPACITY) {
            if opacity.is_some() || !channel_definition_records.is_empty() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            opacity = Some(parse_layer_opacity(child, base_offset)?);
        } else if child_type.equals(BoxType::CHANNEL_DEFINITION) {
            if !channel_definition_records.is_empty() || opacity.is_some() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            channel_definition_records = parse_channel_definition(child, u16::MAX, base_offset)?;
        } else {
            let (count, _) = inspect_metadata_box(child, limits, 1, u32::MAX - 1)?;
            nested_metadata_boxes = nested_metadata_boxes.checked_add(count).ok_or_else(|| {
                DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
            })?;
        }
    }
    Ok(CompositingLayer {
        header: box_ref.header,
        payload: box_ref.payload,
        horizontal_grid_size,
        vertical_grid_size,
        registrations,
        color_group,
        channel_definition_records,
        opacity,
        nested_metadata_boxes,
    })
}

#[allow(clippy::manual_is_multiple_of)]
fn parse_codestream_registration(
    box_ref: BoxRef<'_>,
    base_offset: u64,
    limits: &ResourceLimits,
) -> Result<(u16, u16, Vec<CodestreamRegistration>), DecodeError> {
    if box_ref.payload.len() < 10 || (box_ref.payload.len() - 4) % 6 != 0 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let horizontal_grid_size = read_u16([box_ref.payload[0], box_ref.payload[1]]);
    let vertical_grid_size = read_u16([box_ref.payload[2], box_ref.payload[3]]);
    if horizontal_grid_size == 0 || vertical_grid_size == 0 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxContents,
        ));
    }
    let count = (box_ref.payload.len() - 4) / 6;
    if count as u64 > u64::from(limits.maximum_codestreams()) {
        return Err(DecodeError::limit(
            Resource::Codestreams,
            u64::from(limits.maximum_codestreams()),
            count as u64,
        ));
    }
    let mut registrations = Vec::with_capacity(count);
    let mut position = 4_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= box_ref.payload.len(),
            decreases box_ref.payload.len() - position,
        )
    )]
    while position < box_ref.payload.len() {
        let horizontal_subsampling = byte_at_checked(box_ref.payload, position, 2, base_offset)?;
        let vertical_subsampling = byte_at_checked(box_ref.payload, position, 3, base_offset)?;
        let horizontal_offset = byte_at_checked(box_ref.payload, position, 4, base_offset)?;
        let vertical_offset = byte_at_checked(box_ref.payload, position, 5, base_offset)?;
        if horizontal_subsampling == 0
            || vertical_subsampling == 0
            || u16::from(horizontal_offset) >= horizontal_grid_size
            || u16::from(vertical_offset) >= vertical_grid_size
        {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
        registrations.push(CodestreamRegistration {
            codestream_index: read_u16([
                byte_at_checked(box_ref.payload, position, 0, base_offset)?,
                byte_at_checked(box_ref.payload, position, 1, base_offset)?,
            ]),
            horizontal_subsampling,
            vertical_subsampling,
            horizontal_offset: u32::from(horizontal_offset),
            vertical_offset: u32::from(vertical_offset),
        });
        position = position.checked_add(6).ok_or_else(|| {
            DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
        })?;
        if position > box_ref.payload.len() {
            return Err(DecodeError::malformed(
                base_offset,
                MalformedKind::InvalidBoxLength,
            ));
        }
    }
    Ok((horizontal_grid_size, vertical_grid_size, registrations))
}

fn parse_color_group(
    box_ref: BoxRef<'_>,
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<Vec<ColorSpecification>, DecodeError> {
    let mut reader = BoxReader::new(box_ref.payload, limits)?;
    let mut colors = Vec::new();
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(decreases box_ref.payload.len() as int - reader.position as int,)
    )]
    loop {
        let previous_position = reader.position;
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if reader.position <= previous_position || reader.position > box_ref.payload.len() {
            return Err(DecodeError::malformed(
                add_offset(base_offset, previous_position as u64)?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let child = next.map_err(|error| rebase_error(error, base_offset))?;
        if !child.header.box_type().equals(BoxType::COLOR_SPECIFICATION) {
            return Err(DecodeError::malformed(
                add_offset(base_offset, child.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
        colors.push(parse_color_specification(child, base_offset)?);
        if colors.len() as u64 > u64::from(limits.maximum_components()) {
            return Err(DecodeError::limit(
                Resource::Components,
                u64::from(limits.maximum_components()),
                colors.len() as u64,
            ));
        }
    }
    if colors.is_empty() {
        return Err(DecodeError::malformed(
            base_offset,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    Ok(colors)
}

fn parse_layer_opacity(box_ref: BoxRef<'_>, base_offset: u64) -> Result<LayerOpacity, DecodeError> {
    let offset = add_offset(base_offset, box_ref.header.offset())?;
    let Some(opacity_type) = box_ref.payload.first() else {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxLength,
        ));
    };
    match *opacity_type {
        0 if box_ref.payload.len() == 1 => Ok(LayerOpacity::Straight),
        1 if box_ref.payload.len() == 1 => Ok(LayerOpacity::Premultiplied),
        2 => {
            if box_ref.payload.len() < 3 {
                return Err(DecodeError::malformed(
                    offset,
                    MalformedKind::InvalidBoxLength,
                ));
            }
            let channels = box_ref.payload[1];
            if channels == 0 {
                return Err(DecodeError::malformed(
                    offset,
                    MalformedKind::InvalidBoxContents,
                ));
            }
            Ok(LayerOpacity::ChromaKey {
                channels,
                values: copy_bytes(&box_ref.payload[2..])?,
            })
        }
        0..=2 => Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxLength,
        )),
        _ => Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxContents,
        )),
    }
}

#[allow(clippy::manual_is_multiple_of)]
fn parse_instruction_set(
    box_ref: BoxRef<'_>,
    composition: (u32, u32, u8),
    base_offset: u64,
    limits: &ResourceLimits,
) -> Result<CompositionInstructionSet, DecodeError> {
    let offset = add_offset(base_offset, box_ref.header.offset())?;
    if box_ref.payload.len() < 8 {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let flags = read_u16([box_ref.payload[0], box_ref.payload[1]]);
    if flags & !0x0027 != 0 {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxContents,
        ));
    }
    let repeat = read_u16([box_ref.payload[2], box_ref.payload[3]]);
    let tick = read_u32([
        box_ref.payload[4],
        box_ref.payload[5],
        box_ref.payload[6],
        box_ref.payload[7],
    ]);
    let have_target_position = flags & 1 != 0;
    let have_target_size = flags & 2 != 0;
    let have_life = flags & 4 != 0;
    let have_source_region = flags & 32 != 0;
    let mut words = 0_usize;
    if have_target_position {
        words = words
            .checked_add(2)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    }
    if have_target_size {
        words = words
            .checked_add(2)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    }
    if have_life {
        words = words
            .checked_add(2)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    }
    if have_source_region {
        words = words
            .checked_add(4)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    }
    let record_bytes = words
        .checked_mul(4)
        .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    let remaining = box_ref.payload.len() - 8;
    if record_bytes == 0 {
        if remaining != 0 {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::InvalidBoxLength,
            ));
        }
        return Ok(CompositionInstructionSet {
            flags,
            repeat,
            tick,
            instructions: Vec::new(),
        });
    }
    if remaining % record_bytes != 0 {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let count = remaining / record_bytes;
    if count as u64 > limits.maximum_work_units() {
        return Err(DecodeError::limit(
            Resource::WorkUnits,
            limits.maximum_work_units(),
            count as u64,
        ));
    }
    let mut instructions = Vec::with_capacity(count);
    let mut position = 8_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= box_ref.payload.len(),
            decreases box_ref.payload.len() - position,
        )
    )]
    while position < box_ref.payload.len() {
        let record_end = position
            .checked_add(record_bytes)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
        if record_end > box_ref.payload.len() {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::InvalidBoxLength,
            ));
        }
        if record_end <= position {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
        let mut cursor = position;
        let mut target_x = 0;
        let mut target_y = 0;
        let mut target_width = composition.0;
        let mut target_height = composition.1;
        let mut life_value = 0;
        let mut persistent = true;
        let mut next_reuse = 0;
        let mut source_x = 0;
        let mut source_y = 0;
        let mut source_width = 0;
        let mut source_height = 0;
        if have_target_position {
            target_x = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            target_y = read_u32_at(box_ref.payload, &mut cursor, offset)?;
        }
        if have_target_size {
            target_width = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            target_height = read_u32_at(box_ref.payload, &mut cursor, offset)?;
        }
        if have_life {
            let encoded_life = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            persistent = encoded_life & 0x8000_0000 != 0;
            life_value = encoded_life & 0x7fff_ffff;
            next_reuse = read_u32_at(box_ref.payload, &mut cursor, offset)?;
        }
        if have_source_region {
            source_x = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            source_y = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            source_width = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            source_height = read_u32_at(box_ref.payload, &mut cursor, offset)?;
        }
        if cursor != record_end {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::InvalidBoxLength,
            ));
        }
        if target_width == 0
            || target_height == 0
            || (have_source_region && (source_width == 0 || source_height == 0))
        {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::InvalidImageGeometry,
            ));
        }
        let life = life_value
            .checked_mul(tick)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
        instructions.push(CompositionInstruction {
            target_x,
            target_y,
            target_width,
            target_height,
            life,
            persistent,
            next_reuse,
            source_x,
            source_y,
            source_width,
            source_height,
        });
        position = record_end;
    }
    Ok(CompositionInstructionSet {
        flags,
        repeat,
        tick,
        instructions,
    })
}

fn read_u32_at(input: &[u8], position: &mut usize, offset: u64) -> Result<u32, DecodeError> {
    let end = position
        .checked_add(4)
        .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    let bytes = input
        .get(*position..end)
        .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::InvalidBoxLength))?;
    *position = end;
    Ok(read_u32([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

pub(super) fn parse_composition(
    box_ref: BoxRef<'_>,
    limits: &ResourceLimits,
) -> Result<Composition, DecodeError> {
    let base_offset = box_ref.header.payload_offset()?;
    let mut reader = BoxReader::new(box_ref.payload, limits)?;
    let mut options = None;
    let mut instruction_sets = Vec::new();
    let mut has_unknown_boxes = false;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(decreases box_ref.payload.len() as int - reader.position as int,)
    )]
    loop {
        let previous_position = reader.position;
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if reader.position <= previous_position || reader.position > box_ref.payload.len() {
            return Err(DecodeError::malformed(
                add_offset(base_offset, previous_position as u64)?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let child = next.map_err(|error| rebase_error(error, base_offset))?;
        let child_type = child.header.box_type();
        if child_type.equals(BoxType::COMPOSITION_OPTIONS) {
            if options.is_some() || !instruction_sets.is_empty() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            if child.payload.len() != 9 {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxLength,
                ));
            }
            let height = read_u32([
                child.payload[0],
                child.payload[1],
                child.payload[2],
                child.payload[3],
            ]);
            let width = read_u32([
                child.payload[4],
                child.payload[5],
                child.payload[6],
                child.payload[7],
            ]);
            validate_dimensions(width, height, limits, base_offset)?;
            options = Some((width, height, child.payload[8]));
        } else if child_type.equals(BoxType::INSTRUCTION_SET) {
            if options.is_none() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let instruction_set = parse_instruction_set(
                child,
                options.ok_or_else(|| {
                    DecodeError::malformed(base_offset, MalformedKind::MissingRequiredStructure)
                })?,
                base_offset,
                limits,
            )?;
            let actual = instruction_sets.len().checked_add(1).ok_or_else(|| {
                DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
            })?;
            if actual as u64 > u64::from(limits.maximum_layers()) {
                return Err(DecodeError::limit(
                    Resource::Layers,
                    u64::from(limits.maximum_layers()),
                    actual as u64,
                ));
            }
            instruction_sets.push(instruction_set);
        } else {
            has_unknown_boxes = true;
        }
    }
    let (width, height, encoded_loop_count) = options.ok_or_else(|| {
        DecodeError::malformed(base_offset, MalformedKind::MissingRequiredStructure)
    })?;
    let loop_count = if encoded_loop_count == u8::MAX {
        0
    } else {
        encoded_loop_count
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?
    };
    Ok(Composition {
        width,
        height,
        loop_count,
        instruction_sets,
        has_unknown_boxes,
    })
}

fn validate_dimensions(
    width: u32,
    height: u32,
    limits: &ResourceLimits,
    offset: u64,
) -> Result<(), DecodeError> {
    if width == 0 || height == 0 {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidImageGeometry,
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
    let pixels = u64::from(width)
        .checked_mul(u64::from(height))
        .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    if pixels > limits.maximum_pixels() {
        return Err(DecodeError::limit(
            Resource::Pixels,
            limits.maximum_pixels(),
            pixels,
        ));
    }
    Ok(())
}

pub(super) fn validate_layer_references(
    layers: &[CompositingLayer<'_>],
    codestream_count: usize,
) -> Result<(), DecodeError> {
    let mut layer_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant layer_index <= layers.len(),
            decreases layers.len() - layer_index,
        )
    )]
    while layer_index < layers.len() {
        let layer = layers
            .get(layer_index)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        if layer.registrations.is_empty() {
            if layer_index >= codestream_count {
                return Err(DecodeError::malformed(
                    layer.header.offset(),
                    MalformedKind::InvalidBoxContents,
                ));
            }
        } else {
            let mut registration_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant registration_index <= layer.registrations.len(),
                    decreases layer.registrations.len() - registration_index,
                )
            )]
            while registration_index < layer.registrations.len() {
                let registration = layer
                    .registrations
                    .get(registration_index)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                if usize::from(registration.codestream_index) >= codestream_count {
                    return Err(DecodeError::malformed(
                        layer.header.offset(),
                        MalformedKind::InvalidBoxContents,
                    ));
                }
                registration_index = registration_index
                    .checked_add(1)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            }
        }
        layer_index = layer_index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    Ok(())
}
