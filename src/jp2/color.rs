//! Colour profiles, palette samples, component mappings, and channel definitions.

use super::{
    BoxRef, ChannelAssociation, ChannelDefinition, ChannelDefinitionRecord, ChannelType,
    ColorMethod, ColorSpecification, ComponentBitDepth, ComponentMapping, DecodeError,
    MalformedKind, MappingType, Palette, PaletteColumn, Resource, ResourceLimits, add_offset,
    parse_bit_depth, read_u16, read_u32,
};
#[cfg(verus_keep_ghost)]
use super::{color_specification_method, palette_view};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl ColorSpecification {
    pub const fn enumerated(color_space: u32) -> Self {
        Self {
            method: ColorMethod::Enumerated { color_space },
            precedence: 0,
            approximation: 0,
            icc_profile: None,
        }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(method => ensures method == color_specification_method(self),)
    )]
    pub const fn method(&self) -> ColorMethod {
        self.method
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::optional_profile_bytes(result) == super::full_color_specification_view(self).3,
    ))]
    pub fn icc_profile(&self) -> Option<&[u8]> {
        match &self.icc_profile {
            Some(profile) => Some(profile.as_slice()),
            None => None,
        }
    }
}

impl Palette {
    #[cfg(test)]
    pub(crate) fn for_test(entries: u16, columns: Vec<PaletteColumn>, values: Vec<i64>) -> Self {
        Self {
            entries,
            columns,
            values,
        }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == palette_view(self).0,)
    )]
    pub const fn entries(&self) -> u16 {
        self.entries
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value@ == palette_view(self).1,)
    )]
    pub fn columns(&self) -> &[PaletteColumn] {
        &self.columns
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures result == crate::specs::part2_palette_value(palette_view(self), entry, column),
        )
    )]
    pub fn value(&self, entry: u16, column: u8) -> Result<i64, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(palette_view);
            reveal(crate::specs::part2_palette_value);
        }
        let columns = match u8::try_from(self.columns.len()) {
            Ok(columns) => columns,
            Err(_) => return Err(palette_value_error(true)),
        };
        if !crate::refinement::palette_coordinates_valid(entry, self.entries, column, columns) {
            return Err(palette_value_error(false));
        }
        let row = match usize::from(entry).checked_mul(self.columns.len()) {
            Some(row) => row,
            None => return Err(palette_value_error(true)),
        };
        let index = match row.checked_add(usize::from(column)) {
            Some(index) => index,
            None => return Err(palette_value_error(true)),
        };
        match self.values.get(index) {
            Some(value) => Ok(*value),
            None => Err(palette_value_error(false)),
        }
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_composition_error(arithmetic),
    )
)]
fn palette_value_error(arithmetic: bool) -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: if arithmetic {
            MalformedKind::ArithmeticOverflow
        } else {
            MalformedKind::InvalidBoxContents
        },
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::color_specification_outcome(result) == crate::specs::part2_parse_color_specification(
        super::box_reference_view(box_ref), base_offset),
))]
pub(super) fn parse_color_specification(
    box_ref: BoxRef<'_>,
    base_offset: u64,
) -> Result<ColorSpecification, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_parse_color_specification); }
    if box_ref.payload.len() < 3 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let profile_bytes = u64::try_from(box_ref.payload.len() - 3)
        .map_err(|_| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    let method_value = box_ref.payload[0];
    let mut icc_profile = None;
    let method = if method_value == 1 {
        if box_ref.payload.len() != 7 {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        ColorMethod::Enumerated {
            color_space: read_u32([
                box_ref.payload[3],
                box_ref.payload[4],
                box_ref.payload[5],
                box_ref.payload[6],
            ]),
        }
    } else if method_value == 2 {
        if profile_bytes == 0 {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        icc_profile = Some(copy_profile(&box_ref.payload[3..])?);
        ColorMethod::RestrictedIcc { profile_bytes }
    } else if method_value == 3 {
        if profile_bytes == 0 {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        icc_profile = Some(copy_profile(&box_ref.payload[3..])?);
        ColorMethod::AnyIcc { profile_bytes }
    } else {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidColorSpecification,
        ));
    };
    Ok(ColorSpecification {
        method,
        precedence: box_ref.payload[1],
        approximation: box_ref.payload[2],
        icc_profile,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.is_ok(), result.ok().unwrap()@ == source@,
))]
fn copy_profile(source: &[u8]) -> Result<Vec<u8>, DecodeError> {
    let mut profile = Vec::with_capacity(source.len());
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= source.len(),
                profile@ == source@.take(index as int),
            decreases source.len() - index,
        )
    )]
    while index < source.len() {
        profile.push(
            *source
                .get(index)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?,
        );
        index = index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    Ok(profile)
}

pub(super) fn parse_palette(box_ref: BoxRef<'_>, base_offset: u64) -> Result<Palette, DecodeError> {
    if box_ref.payload.len() < 3 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let entries = read_u16([box_ref.payload[0], box_ref.payload[1]]);
    let columns = box_ref.payload[2];
    if entries == 0 || columns == 0 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxContents,
        ));
    }
    let descriptor_end = 3_usize
        .checked_add(usize::from(columns))
        .ok_or_else(|| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    if descriptor_end > box_ref.payload.len() {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let mut columns = Vec::with_capacity(usize::from(columns));
    let mut bytes_per_entry = 0_usize;
    let mut descriptor = 3_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant descriptor <= descriptor_end,
            decreases descriptor_end - descriptor,
        )
    )]
    while descriptor < descriptor_end {
        if descriptor >= box_ref.payload.len() {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let bit_depth = parse_bit_depth(box_ref.payload[descriptor], base_offset)?;
        let (bits, signed) = match bit_depth {
            ComponentBitDepth::Uniform { bits, signed } => (bits, signed),
            ComponentBitDepth::Variable => {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxContents,
                ));
            }
        };
        let component_bytes = usize::from(bits).checked_add(7).ok_or_else(|| {
            DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
        })? / 8;
        bytes_per_entry = bytes_per_entry
            .checked_add(component_bytes)
            .ok_or_else(|| {
                DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
            })?;
        columns.push(PaletteColumn {
            precision: bits,
            signed,
        });
        descriptor = descriptor.checked_add(1).ok_or_else(|| {
            DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
        })?;
    }
    let sample_bytes = usize::from(entries)
        .checked_mul(bytes_per_entry)
        .ok_or_else(|| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    let expected_length = descriptor_end
        .checked_add(sample_bytes)
        .ok_or_else(|| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    if box_ref.payload.len() != expected_length {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let value_count = usize::from(entries)
        .checked_mul(columns.len())
        .ok_or_else(|| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    let mut values = Vec::with_capacity(value_count);
    let mut offset = descriptor_end;
    let mut entry = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant entry <= entries,
            decreases entries - entry,
        )
    )]
    while entry < entries {
        let mut column = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant column <= columns.len(),
                decreases columns.len() - column,
            )
        )]
        while column < columns.len() {
            let descriptor = columns.get(column).ok_or_else(|| {
                DecodeError::malformed(base_offset, MalformedKind::InvalidBoxContents)
            })?;
            let byte_count = usize::from(descriptor.precision)
                .checked_add(7)
                .ok_or_else(|| {
                    DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
                })?
                / 8;
            let end = offset.checked_add(byte_count).ok_or_else(|| {
                DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
            })?;
            if end > box_ref.payload.len() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxLength,
                ));
            }
            values.push(parse_palette_value(
                &box_ref.payload[offset..end],
                descriptor.precision,
                descriptor.signed,
                base_offset,
            )?);
            offset = end;
            column = column.checked_add(1).ok_or_else(|| {
                DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
            })?;
        }
        entry = entry.checked_add(1).ok_or_else(|| {
            DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
        })?;
    }
    if offset != box_ref.payload.len() || values.len() != value_count {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    Ok(Palette {
        entries,
        columns,
        values,
    })
}

pub(super) fn parse_component_mapping(
    box_ref: BoxRef<'_>,
    components: u16,
    palette_columns: u8,
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<Vec<ComponentMapping>, DecodeError> {
    if box_ref.payload.is_empty() || !box_ref.payload.len().is_multiple_of(4) {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let entry_count = box_ref.payload.len() / 4;
    let entries = u16::try_from(entry_count)
        .map_err(|_| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    if entries > limits.maximum_components() {
        return Err(DecodeError::limit(
            Resource::Components,
            u64::from(limits.maximum_components()),
            u64::from(entries),
        ));
    }
    let mut mappings = Vec::with_capacity(entry_count);
    let mut offset = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant offset <= box_ref.payload.len(),
            decreases box_ref.payload.len() - offset,
        )
    )]
    while offset < box_ref.payload.len() {
        if box_ref.payload.len() - offset < 4 {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let component = read_u16([box_ref.payload[offset], box_ref.payload[offset + 1]]);
        let mapping_type = box_ref.payload[offset + 2];
        let palette_column = box_ref.payload[offset + 3];
        if !crate::refinement::component_mapping_valid(
            component,
            components,
            mapping_type,
            palette_column,
            palette_columns,
        ) {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
        let mapping_type = if mapping_type == 0 {
            MappingType::Direct
        } else {
            MappingType::Palette {
                column: palette_column,
            }
        };
        mappings.push(ComponentMapping {
            component,
            mapping_type,
        });
        offset = offset.checked_add(4).ok_or_else(|| {
            DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
        })?;
    }
    Ok(mappings)
}

pub(super) fn parse_channel_definition(
    box_ref: BoxRef<'_>,
    output_channels: u16,
    base_offset: u64,
) -> Result<Vec<ChannelDefinitionRecord>, DecodeError> {
    if box_ref.payload.len() < 2 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let entries = read_u16([box_ref.payload[0], box_ref.payload[1]]);
    let entry_bytes = usize::from(entries)
        .checked_mul(6)
        .ok_or_else(|| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    let expected_length = 2_usize
        .checked_add(entry_bytes)
        .ok_or_else(|| DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow))?;
    if entries == 0 || box_ref.payload.len() != expected_length {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let mut records = Vec::with_capacity(usize::from(entries));
    let mut offset = 2_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant offset <= box_ref.payload.len(),
            decreases box_ref.payload.len() - offset,
        )
    )]
    while offset < box_ref.payload.len() {
        if box_ref.payload.len() - offset < 6 {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let channel = read_u16([box_ref.payload[offset], box_ref.payload[offset + 1]]);
        let channel_type = read_u16([box_ref.payload[offset + 2], box_ref.payload[offset + 3]]);
        let association = read_u16([box_ref.payload[offset + 4], box_ref.payload[offset + 5]]);
        if !crate::refinement::channel_definition_valid(
            channel,
            channel_type,
            association,
            output_channels,
        ) {
            return Err(DecodeError::malformed(
                add_offset(base_offset, box_ref.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
        let channel_type = match channel_type {
            0 => ChannelType::Color,
            1 => ChannelType::Opacity,
            2 => ChannelType::PremultipliedOpacity,
            0xffff => ChannelType::Unspecified,
            _ => unreachable!("channel type validated above"),
        };
        let association = if association == 0 {
            ChannelAssociation::WholeImage
        } else if association == 0xffff {
            ChannelAssociation::Unassociated
        } else {
            ChannelAssociation::Color(association)
        };
        records.push(ChannelDefinitionRecord {
            channel,
            definition: ChannelDefinition::new(channel_type, association),
        });
        offset = offset.checked_add(6).ok_or_else(|| {
            DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow)
        })?;
    }
    Ok(records)
}

fn parse_palette_value(
    bytes: &[u8],
    precision: u8,
    signed: bool,
    offset: u64,
) -> Result<i64, DecodeError> {
    if precision == 0 || precision > 38 || bytes.is_empty() || bytes.len() > 5 {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxContents,
        ));
    }
    let mut raw = 0_u64;
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= bytes.len(),
            decreases bytes.len() - index,
        )
    )]
    while index < bytes.len() {
        raw = raw
            .checked_mul(256)
            .and_then(|value| value.checked_add(u64::from(bytes[index])))
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
        index = index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    }
    let mut modulus = 1_u64;
    let mut bit = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant bit <= precision,
            decreases precision - bit,
        )
    )]
    while bit < precision {
        modulus = modulus
            .checked_mul(2)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
        bit = bit
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    }
    let mask = modulus
        .checked_sub(1)
        .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
    let value = raw & mask;
    if signed && value & (modulus >> 1) != 0 {
        let magnitude =
            i64::try_from(modulus.checked_sub(value).ok_or_else(|| {
                DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow)
            })?)
            .map_err(|_| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))?;
        0_i64
            .checked_sub(magnitude)
            .ok_or_else(|| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))
    } else {
        i64::try_from(value)
            .map_err(|_| DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow))
    }
}
