//! Ordered actual raw component mappings and channel-definition records.

use super::*;

verus! {

pub type Part2ChannelRecord = (u16, (crate::ChannelType, crate::ChannelAssociation));

pub open spec fn part2_mapping_entry(
    input: Part2BoxReference, components: u16, palette_columns: u8, base: u64, index: nat,
) -> Result<crate::jp2::ComponentMapping, crate::DecodeError> {
    let offset = index * 4;
    let payload = input.1;
    if offset + 4 > payload.len() {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
    } else {
        let component = part2_box_u16([payload[offset as int], payload[offset as int + 1]]);
        let kind = payload[offset as int + 2];
        let column = payload[offset as int + 3];
        if !part2_component_mapping_valid(component, components, kind, column, palette_columns) {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
        } else {
            Ok(crate::jp2::ComponentMapping { component,
                mapping_type: if kind == 0 { crate::jp2::MappingType::Direct }
                    else { crate::jp2::MappingType::Palette { column } } })
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_mapping_prefix(
    input: Part2BoxReference, components: u16, palette_columns: u8, base: u64, count: nat,
) -> Result<Seq<crate::jp2::ComponentMapping>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) }
    else {
        match part2_mapping_prefix(input, components, palette_columns, base, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(records) => match part2_mapping_entry(input, components, palette_columns, base, (count - 1) as nat) {
                Err(error) => Err(error), Ok(record) => Ok(records.push(record)),
            },
        }
    }
}

pub open spec fn part2_parse_component_mapping(
    input: Part2BoxReference, components: u16, palette_columns: u8, limits: &crate::ResourceLimits, base: u64,
) -> Result<Seq<crate::jp2::ComponentMapping>, crate::DecodeError> {
    let length = input.1.len();
    let count = length / 4;
    if length == 0 || length % 4 != 0 {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
    } else if count > u16::MAX as nat {
        Err(crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::ArithmeticOverflow })
    } else if count > crate::limits::resource_component_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Components,
            limit: crate::limits::resource_component_limit(limits) as u64, actual: count as u64 })
    } else { part2_mapping_prefix(input, components, palette_columns, base, count) }
}

pub(crate) proof fn part2_mapping_step(
    input: Part2BoxReference, components: u16, palette_columns: u8, base: u64, count: nat,
)
    ensures part2_mapping_prefix(input, components, palette_columns, base, count + 1)
        == match part2_mapping_prefix(input, components, palette_columns, base, count) {
            Err(error) => Err(error),
            Ok(records) => match part2_mapping_entry(input, components, palette_columns, base, count) {
                Err(error) => Err(error), Ok(record) => Ok(records.push(record)),
            },
        },
{
    reveal(part2_mapping_prefix);
}

pub(crate) proof fn part2_mapping_error(
    input: Part2BoxReference, components: u16, palette_columns: u8, base: u64, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_mapping_prefix(input, components, palette_columns, base, count) {
        Err(error) => part2_mapping_prefix(input, components, palette_columns, base, total) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_mapping_prefix);
    if count < total { part2_mapping_error(input, components, palette_columns, base, count, (total - 1) as nat); }
}

pub open spec fn part2_channel_record(
    input: Part2BoxReference, output_channels: u16, base: u64, index: nat,
) -> Result<Part2ChannelRecord, crate::DecodeError> {
    let offset = 2 + index * 6;
    let payload = input.1;
    if offset + 6 > payload.len() {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
    } else {
        let channel = part2_box_u16([payload[offset as int], payload[offset as int + 1]]);
        let kind = part2_box_u16([payload[offset as int + 2], payload[offset as int + 3]]);
        let association = part2_box_u16([payload[offset as int + 4], payload[offset as int + 5]]);
        if !part2_channel_definition_valid(channel, kind, association, output_channels) {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
        } else {
            Ok((channel, (if kind == 0 { crate::ChannelType::Color }
                else if kind == 1 { crate::ChannelType::Opacity }
                else if kind == 2 { crate::ChannelType::PremultipliedOpacity }
                else { crate::ChannelType::Unspecified },
                if association == 0 { crate::ChannelAssociation::WholeImage }
                else if association == 0xffff { crate::ChannelAssociation::Unassociated }
                else { crate::ChannelAssociation::Color(association) })))
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_channel_records_prefix(
    input: Part2BoxReference, output_channels: u16, base: u64, count: nat,
) -> Result<Seq<Part2ChannelRecord>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) }
    else {
        match part2_channel_records_prefix(input, output_channels, base, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(records) => match part2_channel_record(input, output_channels, base, (count - 1) as nat) {
                Err(error) => Err(error), Ok(record) => Ok(records.push(record)),
            },
        }
    }
}

pub open spec fn part2_parse_channel_definition(
    input: Part2BoxReference, output_channels: u16, base: u64,
) -> Result<Seq<Part2ChannelRecord>, crate::DecodeError> {
    let payload = input.1;
    if payload.len() < 2 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)) }
    else {
        let entries = part2_box_u16([payload[0], payload[1]]);
        if entries == 0 || payload.len() != 2 + entries as nat * 6 {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
        } else { part2_channel_records_prefix(input, output_channels, base, entries as nat) }
    }
}

pub(crate) proof fn part2_channel_records_step(
    input: Part2BoxReference, output_channels: u16, base: u64, count: nat,
)
    ensures part2_channel_records_prefix(input, output_channels, base, count + 1)
        == match part2_channel_records_prefix(input, output_channels, base, count) {
            Err(error) => Err(error),
            Ok(records) => match part2_channel_record(input, output_channels, base, count) {
                Err(error) => Err(error), Ok(record) => Ok(records.push(record)),
            },
        },
{
    reveal(part2_channel_records_prefix);
}

pub(crate) proof fn part2_channel_records_error(
    input: Part2BoxReference, output_channels: u16, base: u64, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_channel_records_prefix(input, output_channels, base, count) {
        Err(error) => part2_channel_records_prefix(input, output_channels, base, total) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_channel_records_prefix);
    if count < total { part2_channel_records_error(input, output_channels, base, count, (total - 1) as nat); }
}

}
