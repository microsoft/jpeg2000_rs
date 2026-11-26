//! Compositing layers, registration, opacity, and composition instructions.

use super::{
    BoxHeader, BoxRef, BoxType, ChannelDefinitionRecord, CodestreamRegistration,
    ColorSpecification, CompositingLayer, Composition, CompositionInstruction,
    CompositionInstructionSet, DecodeError, LayerOpacity, MalformedKind, Resource, ResourceLimits,
    add_offset, box_reader_from_input, byte_at_checked, copy_bytes, inspect_metadata_box,
    parse_channel_definition, parse_color_specification, read_u16, read_u32, rebase_error,
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

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::raw_compositing_layer_payload_reference(self),
    ))]
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

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == super::source_layer_registrations(self),
    ))]
    pub fn registrations(&self) -> &[CodestreamRegistration] {
        &self.registrations
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == (super::source_layer_color_group(self).len() > 0),
    ))]
    pub const fn has_color_group(&self) -> bool {
        !self.color_group.is_empty()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::source_layer_opacity(self).is_some(),
    ))]
    pub const fn has_opacity_box(&self) -> bool {
        self.opacity.is_some()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == super::source_layer_color_group(self),
    ))]
    pub fn color_group(&self) -> &[ColorSpecification] {
        &self.color_group
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == super::source_layer_definition_records(self),
    ))]
    pub fn channel_definition_records(&self) -> &[ChannelDefinitionRecord] {
        &self.channel_definition_records
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::source_opacity_reference_view(result) == super::source_layer_opacity(self),
    ))]
    pub const fn opacity(&self) -> Option<&LayerOpacity> {
        self.opacity.as_ref()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::source_layer_nested_metadata(self),
    ))]
    pub const fn nested_metadata_boxes(&self) -> u32 {
        self.nested_metadata_boxes
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_layer_header_storage_result(super::box_reference_view(box_ref),*limits,super::raw_compositing_layer_outcome(result)),
    super::raw_compositing_layer_outcome(result) != Err(DecodeError::AllocationFailed) ==> super::raw_compositing_layer_outcome(result)
        == crate::specs::part2_parse_compositing_layer(super::box_reference_view(box_ref), *limits),
        match &result { Err(_) => true, Ok(layer) => super::raw_compositing_layer_payload_reference(layer) == box_ref.payload },
))]
pub(super) fn parse_compositing_layer<'a>(
    box_ref: BoxRef<'a>,
    limits: &ResourceLimits,
) -> Result<CompositingLayer<'a>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_layer_header_storage_normal(super::box_reference_view(box_ref),*limits); }
    let base_offset = box_ref.header.payload_offset()?;
    let mut reader = box_reader_from_input(box_ref.payload, limits)?;
    let mut horizontal_grid_size = 1_u16;
    let mut vertical_grid_size = 1_u16;
    let mut registrations = Vec::new();
    let mut has_registration = false;
    let mut color_group = Vec::new();
    let mut channel_definition_records = Vec::new();
    let mut opacity = None;
    let mut nested_metadata_boxes = 0_u32;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_parse_compositing_layer(
    super::box_reference_view(box_ref), *limits); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost machine=crate::specs::part2_layer_header_storage_machine(box_ref.payload@,*limits,base_offset);
        let ghost root=|events:Seq<crate::specs::Part2JpipSnapshotEvent>|crate::specs::part2_layer_header_storage_run(super::box_reference_view(box_ref),*limits,events);
        let ghost mut storage_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(registrations@ =~= Seq::<CodestreamRegistration>::empty());
        assert(super::full_color_group_view(color_group@) =~= Seq::<crate::specs::Part2ColorSpecification>::empty());
        assert(super::channel_definition_records_view(channel_definition_records@) =~= Seq::<crate::specs::Part2ChannelRecord>::empty());
        crate::specs::part2_header_storage_machines_valid(box_ref.payload@,*limits,base_offset,false);
        assert forall|tail:Seq<crate::specs::Part2JpipSnapshotEvent>|root(storage_prefix+tail)
            ==crate::specs::part2_header_storage_boxes_run(machine,super::box_reader_state(&reader),
                super::raw_compositing_layer_state(box_ref,horizontal_grid_size,vertical_grid_size,
                    registrations@,color_group@,channel_definition_records@,&opacity,nested_metadata_boxes,has_registration),tail)
            by { assert(storage_prefix+tail =~= tail); }
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant_except_break expected == crate::specs::part2_raw_layer_boxes(
                box_ref.payload@, super::box_reader_state(&reader),
                super::raw_compositing_layer_state(box_ref, horizontal_grid_size, vertical_grid_size,
                    registrations@, color_group@, channel_definition_records@, &opacity, nested_metadata_boxes, has_registration),
                *limits, base_offset),
                expected == crate::specs::part2_parse_compositing_layer(super::box_reference_view(box_ref), *limits),
                crate::specs::part2_layer_header_storage_result(super::box_reference_view(box_ref),*limits,expected),
                machine==crate::specs::part2_layer_header_storage_machine(box_ref.payload@,*limits,base_offset),
                root==(|events:Seq<crate::specs::Part2JpipSnapshotEvent>|crate::specs::part2_layer_header_storage_run(super::box_reference_view(box_ref),*limits,events)),
                crate::specs::part2_header_storage_machine_valid(machine),
                crate::specs::part2_cold_phase(root,storage_prefix,|events|crate::specs::part2_header_storage_boxes_run(
                    machine,super::box_reader_state(&reader),
                    super::raw_compositing_layer_state(box_ref,horizontal_grid_size,vertical_grid_size,
                        registrations@,color_group@,channel_definition_records@,&opacity,nested_metadata_boxes,has_registration),events)),
            ensures expected == Ok(super::raw_compositing_layer_state(box_ref, horizontal_grid_size, vertical_grid_size,
                registrations@, color_group@, channel_definition_records@, &opacity, nested_metadata_boxes, has_registration).layer),
                crate::specs::part2_layer_header_storage_result(super::box_reference_view(box_ref),*limits,expected),
            decreases box_ref.payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! {
            super::channel_storage_box_kinds_known();
            reveal(crate::specs::part2_raw_layer_boxes); reveal(crate::specs::part2_raw_layer_step);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_reader=super::box_reader_state(&reader);
            let ghost previous_state=super::raw_compositing_layer_state(box_ref,horizontal_grid_size,vertical_grid_size,
                registrations@,color_group@,channel_definition_records@,&opacity,nested_metadata_boxes,has_registration);
        }
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
        let child = next.map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
            ))]
            |error| rebase_error(error, base_offset),
        )?;
        let child_type = child.header.box_type();
        if child_type.equals(BoxType::CODESTREAM_REGISTRATION) {
            if has_registration {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let result = parse_codestream_registration(child, base_offset, limits);
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=result {
                    if error==DecodeError::AllocationFailed {
                        let context=crate::specs::Part2RegistrationStorageContext {
                            input:super::box_reference_view(child),base:base_offset,limits:*limits};
                        crate::specs::part2_header_storage_request_registration_error(context,error);
                        crate::specs::part2_header_storage_root_error(root,storage_prefix,machine,previous_reader,previous_state,
                            super::box_reference_view(child),crate::specs::Part2HeaderStorageRequest::Registration {context},error);
                        crate::specs::part2_layer_header_storage_observed(super::box_reference_view(box_ref),*limits,Err(error));
                    }
                }
            }
            let parsed = result?;
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
            let group_base = add_offset(base_offset, child.header.payload_offset()?)?;
            let parsed = parse_color_group(child, limits, group_base);
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=parsed {
                    if error==DecodeError::AllocationFailed {
                        let context=crate::specs::Part2ColorGroupStorageContext {
                            input:super::box_reference_view(child),limits:*limits,base:group_base};
                        crate::specs::part2_header_storage_request_color_group_error(context,error);
                        crate::specs::part2_header_storage_root_error(root,storage_prefix,machine,previous_reader,previous_state,
                            super::box_reference_view(child),crate::specs::Part2HeaderStorageRequest::ColorGroup {context},error);
                        crate::specs::part2_layer_header_storage_observed(super::box_reference_view(box_ref),*limits,Err(error));
                    }
                }
            }
            color_group = parsed?;
        } else if child_type.equals(BoxType::OPACITY) {
            if opacity.is_some() || !channel_definition_records.is_empty() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let parsed = parse_layer_opacity(child, base_offset);
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=parsed {
                    if error==DecodeError::AllocationFailed {
                        let context=crate::specs::Part2OpacityStorageContext {
                            input:super::box_reference_view(child),base:base_offset};
                        crate::specs::part2_header_storage_request_opacity_error(context,error);
                        crate::specs::part2_header_storage_root_error(root,storage_prefix,machine,previous_reader,previous_state,
                            super::box_reference_view(child),crate::specs::Part2HeaderStorageRequest::Opacity {context},error);
                        crate::specs::part2_layer_header_storage_observed(super::box_reference_view(box_ref),*limits,Err(error));
                    }
                }
            }
            opacity = Some(parsed?);
        } else if child_type.equals(BoxType::CHANNEL_DEFINITION) {
            if !channel_definition_records.is_empty() || opacity.is_some() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, child.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let parsed = parse_channel_definition(child, u16::MAX, base_offset);
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=parsed {
                    if error==DecodeError::AllocationFailed {
                        let context=crate::specs::Part2ChannelStorageContext {
                            input:super::box_reference_view(child),channels:u16::MAX,base:base_offset};
                        crate::specs::part2_header_storage_request_channel_error(context,error);
                        crate::specs::part2_header_storage_root_error(root,storage_prefix,machine,previous_reader,previous_state,
                            super::box_reference_view(child),crate::specs::Part2HeaderStorageRequest::Channel {context},error);
                        crate::specs::part2_layer_header_storage_observed(super::box_reference_view(box_ref),*limits,Err(error));
                    }
                }
            }
            channel_definition_records = parsed?;
        } else {
            let (count, _) = inspect_metadata_box(child, limits, 1, u32::MAX - 1)?;
            nested_metadata_boxes = nested_metadata_boxes.checked_add(count).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                ))]
                || DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
            )?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            storage_prefix=crate::specs::part2_header_storage_root_advance(root,storage_prefix,machine,previous_reader,previous_state,
                super::box_reference_view(child),super::raw_compositing_layer_state(box_ref,horizontal_grid_size,vertical_grid_size,
                    registrations@,color_group@,channel_definition_records@,&opacity,nested_metadata_boxes,has_registration));
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
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_registration_storage_result(crate::specs::Part2RegistrationStorageContext {
        input:super::box_reference_view(box_ref),base:base_offset,limits:*limits,
    },super::registration_outcome(result)),
    super::registration_outcome(result) != Err(DecodeError::AllocationFailed) ==>
        super::registration_outcome(result) == crate::specs::part2_parse_codestream_registration(
        super::box_reference_view(box_ref), base_offset, limits),
))]
pub(super) fn parse_codestream_registration(
    box_ref: BoxRef<'_>,
    base_offset: u64,
    limits: &ResourceLimits,
) -> Result<(u16, u16, Vec<CodestreamRegistration>), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost storage_context=crate::specs::Part2RegistrationStorageContext {
            input:super::box_reference_view(box_ref),base:base_offset,limits:*limits};
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_registration_storage_normal(storage_context); }
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
    let reserved = crate::allocation::empty_with_capacity(count);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_layer_metadata_capacity_observed(
            crate::specs::Part2LayerMetadataCapacityContext::Registration {context:storage_context},
            crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved {crate::specs::part2_registration_storage_refused(storage_context,error);}
    }
    let mut registrations = reserved?;
    let mut position = 4_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_registration_prefix);
        assert(registrations@ =~= Seq::<CodestreamRegistration>::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= box_ref.payload.len(),
                4 <= position,
                box_ref.payload.len() >= 10,
                (box_ref.payload.len() - 4) % 6 == 0,
                (position - 4) % 6 == 0,
                horizontal_grid_size > 0,
                vertical_grid_size > 0,
                horizontal_grid_size == crate::specs::part2_box_u16([box_ref.payload[0], box_ref.payload[1]]),
                vertical_grid_size == crate::specs::part2_box_u16([box_ref.payload[2], box_ref.payload[3]]),
                count == (box_ref.payload.len() - 4) / 6,
                count as u64 <= crate::limits::resource_codestream_limit(limits) as u64,
                storage_context==(crate::specs::Part2RegistrationStorageContext {
                    input:super::box_reference_view(box_ref),base:base_offset,limits:*limits}),
                crate::specs::part2_registration_storage_result(storage_context,
                    crate::specs::part2_parse_codestream_registration(super::box_reference_view(box_ref),base_offset,limits)),
                crate::specs::part2_registration_prefix(super::box_reference_view(box_ref),
                    base_offset, ((position - 4) / 6) as nat) == Ok(registrations@),
            decreases box_ref.payload.len() - position,
        )
    )]
    while position < box_ref.payload.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_registration_step(super::box_reference_view(box_ref),
                base_offset, ((position - 4) / 6) as nat);
            crate::specs::part2_registration_error(super::box_reference_view(box_ref),
                base_offset, ((position - 4) / 6 + 1) as nat, count as nat);
        }
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_color_group_storage_result(crate::specs::Part2ColorGroupStorageContext {
        input:super::box_reference_view(box_ref),limits:*limits,base:base_offset,
    },super::color_group_outcome(result)),
    super::color_group_outcome(result) != Err(DecodeError::AllocationFailed) ==>
        super::color_group_outcome(result) == crate::specs::part2_parse_color_group(
        super::box_reference_view(box_ref), *limits, base_offset),
))]
pub(super) fn parse_color_group(
    box_ref: BoxRef<'_>,
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<Vec<ColorSpecification>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context=crate::specs::Part2ColorGroupStorageContext {
            input:super::box_reference_view(box_ref),limits:*limits,base:base_offset};
        let ghost mut storage_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_color_group_storage_normal(context); }
    let mut reader = box_reader_from_input(box_ref.payload, limits)?;
    let mut colors = Vec::new();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_parse_color_group(
    super::box_reference_view(box_ref), *limits, base_offset); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(super::full_color_group_view(colors@) =~= Seq::<crate::specs::Part2ColorSpecification>::empty());
        assert forall|tail:Seq<crate::specs::Part2JpipSnapshotEvent>|
            crate::specs::part2_color_group_storage_run(context,storage_prefix+tail)
                ==crate::specs::part2_color_group_storage_boxes_run(context,super::box_reader_state(&reader),
                    super::full_color_group_view(colors@),tail) by {assert(storage_prefix+tail =~= tail);}
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant_except_break expected == crate::specs::part2_color_group_boxes(
                box_ref.payload@, super::box_reader_state(&reader), super::full_color_group_view(colors@), *limits, base_offset),
                expected == crate::specs::part2_parse_color_group(super::box_reference_view(box_ref), *limits, base_offset),
                context==(crate::specs::Part2ColorGroupStorageContext {
                    input:super::box_reference_view(box_ref),limits:*limits,base:base_offset}),
                crate::specs::part2_color_group_storage_result(context,expected),
                crate::specs::part2_cold_phase(|events|crate::specs::part2_color_group_storage_run(context,events),storage_prefix,
                    |events|crate::specs::part2_color_group_storage_boxes_run(context,super::box_reader_state(&reader),
                        super::full_color_group_view(colors@),events)),
            ensures expected == crate::specs::part2_color_group_finish(super::full_color_group_view(colors@), base_offset),
                crate::specs::part2_color_group_storage_result(context,expected),
            decreases box_ref.payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_color_group_boxes); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_reader=super::box_reader_state(&reader);
            let ghost previous_colors=super::full_color_group_view(colors@);
        }
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
        let child = next.map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
            ))]
            |error| rebase_error(error, base_offset),
        )?;
        if !child.header.box_type().equals(BoxType::COLOR_SPECIFICATION) {
            return Err(DecodeError::malformed(
                add_offset(base_offset, child.header.offset())?,
                MalformedKind::InvalidBoxContents,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = colors@; }
        let parsed = parse_color_specification(child, base_offset);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=parsed {
                if error==DecodeError::AllocationFailed {
                    crate::specs::part2_color_group_storage_root_error(context,storage_prefix,previous_reader,previous_colors,
                        super::box_reference_view(child),error);
                }
            }
        }
        let color = parsed?;
        let reserved = crate::allocation::reserve_additional(&mut colors, 1);
        #[cfg(verus_keep_ghost)]
        proof! {
            let append=crate::specs::Part2ColorGroupAppendContext {
                group:context,input:super::box_reference_view(child),before:previous_colors,
                parsed:super::full_color_specification_view(&color)};
            crate::specs::part2_color_group_append_capacity_observed(
                append,crate::allocation::inspection_capacity_outcome(reserved));
            if let Err(error)=reserved {
                crate::specs::part2_color_group_storage_root_append_error(append,storage_prefix,previous_reader,error);
            }
        }
        reserved?;
        colors.push(color);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(super::full_color_group_view(colors@) =~=
                super::full_color_group_view(previous).push(super::full_color_specification_view(&colors@[colors@.len() - 1])));
        }
        if colors.len() as u64 > u64::from(limits.maximum_components()) {
            return Err(DecodeError::limit(
                Resource::Components,
                u64::from(limits.maximum_components()),
                colors.len() as u64,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            storage_prefix=crate::specs::part2_color_group_storage_root_advance(context,storage_prefix,previous_reader,previous_colors,
                super::box_reference_view(child),super::full_color_group_view(colors@));
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_opacity_storage_result(crate::specs::Part2OpacityStorageContext {
        input:super::box_reference_view(box_ref),base:base_offset,
    },super::opacity_outcome(result)),
    super::opacity_outcome(result) != Err(DecodeError::AllocationFailed) ==>
        super::opacity_outcome(result) == crate::specs::part2_parse_layer_opacity(
        super::box_reference_view(box_ref), base_offset),
))]
pub(super) fn parse_layer_opacity(
    box_ref: BoxRef<'_>,
    base_offset: u64,
) -> Result<LayerOpacity, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_opacity_storage_normal(crate::specs::Part2OpacityStorageContext {
            input:super::box_reference_view(box_ref),base:base_offset});
    }
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
            let copied = copy_bytes(&box_ref.payload[2..]);
            #[cfg(verus_keep_ghost)]
            proof! {
                let context=crate::specs::Part2OpacityStorageContext {
                    input:super::box_reference_view(box_ref),base:base_offset};
                crate::specs::part2_layer_metadata_capacity_observed(
                    crate::specs::Part2LayerMetadataCapacityContext::Opacity {context},
                    crate::allocation::inspection_capacity_outcome(copied));
                if let Err(error)=copied {crate::specs::part2_opacity_storage_refused(context,error);}
            }
            Ok(LayerOpacity::ChromaKey {
                channels,
                values: copied?,
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
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_instruction_storage_result(crate::specs::Part2InstructionStorageContext {
        input:super::box_reference_view(box_ref),composition,base:base_offset,limits:*limits,
    },super::raw_instruction_set_outcome(result)),
    super::raw_instruction_set_outcome(result) != Err(DecodeError::AllocationFailed) ==>
        super::raw_instruction_set_outcome(result) == crate::specs::part2_parse_instruction_set(
        super::box_reference_view(box_ref), composition, base_offset, limits),
))]
pub(super) fn parse_instruction_set(
    box_ref: BoxRef<'_>,
    composition: (u32, u32, u8),
    base_offset: u64,
    limits: &ResourceLimits,
) -> Result<CompositionInstructionSet, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost storage_context=crate::specs::Part2InstructionStorageContext {
            input:super::box_reference_view(box_ref),composition,base:base_offset,limits:*limits};
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_instruction_storage_normal(storage_context);
        reveal(crate::specs::part2_parse_instruction_set);
    }
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
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(words == crate::specs::part2_instruction_record_words(flags));
        assert(words <= 10);
    }
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
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_instruction_capacity_observed(
            storage_context,crate::allocation::inspection_capacity_outcome(reserved));
        if let Err(error)=reserved {crate::specs::part2_instruction_storage_refused(storage_context,error);}
    }
    let mut instructions = reserved?;
    let mut position = 8_usize;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_parse_instruction_set(
    super::box_reference_view(box_ref), composition, base_offset, limits); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(instructions@ =~= Seq::<CompositionInstruction>::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= box_ref.payload.len(),
                8 <= position,
                box_ref.payload.len() >= 8,
                crate::specs::part2_box_add_offset(base_offset, super::box_reference_view(box_ref).0.1) == Ok(offset),
                flags == crate::specs::part2_box_u16([box_ref.payload[0], box_ref.payload[1]]),
                flags & !0x0027u16 == 0,
                repeat == crate::specs::part2_box_u16([box_ref.payload[2], box_ref.payload[3]]),
                tick == crate::specs::part2_box_u32([box_ref.payload[4], box_ref.payload[5], box_ref.payload[6], box_ref.payload[7]]),
                have_target_position == (flags & 1 != 0),
                have_target_size == (flags & 2 != 0),
                have_life == (flags & 4 != 0),
                have_source_region == (flags & 32 != 0),
                words == crate::specs::part2_instruction_record_words(flags),
                0 < words <= 10,
                record_bytes == words * 4,
                0 < record_bytes <= 40,
                expected == crate::specs::part2_parse_instruction_set(super::box_reference_view(box_ref), composition, base_offset, limits),
                storage_context==(crate::specs::Part2InstructionStorageContext {
                    input:super::box_reference_view(box_ref),composition,base:base_offset,limits:*limits}),
                crate::specs::part2_instruction_storage_result(storage_context,expected),
                expected == crate::specs::part2_instruction_result(flags, repeat, tick,
                    crate::specs::part2_instruction_records(super::box_reference_view(box_ref), composition, offset,
                        flags, tick, position, instructions@)),
            decreases box_ref.payload.len() - position,
        )
    )]
    while position < box_ref.payload.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_instruction_records);
        }
        let record_end = position.checked_add(record_bytes).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(offset),
                ))]
            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
        )?;
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
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost size_start = position as nat + if have_target_position { 8nat } else { 0nat };
            let ghost life_start = size_start + if have_target_size { 8nat } else { 0nat };
            let ghost source_start = life_start + if have_life { 8nat } else { 0nat };
        }
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
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(cursor == size_start);
            assert(target_x == if have_target_position { crate::specs::part2_composition_word_at(box_ref.payload@, position as nat) } else { 0 });
            assert(target_y == if have_target_position { crate::specs::part2_composition_word_at(box_ref.payload@, position as nat + 4) } else { 0 });
        }
        if have_target_size {
            target_width = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            target_height = read_u32_at(box_ref.payload, &mut cursor, offset)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(cursor == life_start);
            assert(target_width == if have_target_size { crate::specs::part2_composition_word_at(box_ref.payload@, size_start) } else { composition.0 });
            assert(target_height == if have_target_size { crate::specs::part2_composition_word_at(box_ref.payload@, size_start + 4) } else { composition.1 });
        }
        if have_life {
            let encoded_life = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            persistent = encoded_life & 0x8000_0000 != 0;
            life_value = encoded_life & 0x7fff_ffff;
            next_reuse = read_u32_at(box_ref.payload, &mut cursor, offset)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(cursor == source_start);
            assert(life_value == if have_life { crate::specs::part2_composition_word_at(box_ref.payload@, life_start) & 0x7fff_ffffu32 } else { 0 });
            assert(persistent == if have_life { crate::specs::part2_composition_word_at(box_ref.payload@, life_start) & 0x8000_0000u32 != 0 } else { true });
            assert(next_reuse == if have_life { crate::specs::part2_composition_word_at(box_ref.payload@, life_start + 4) } else { 0 });
        }
        if have_source_region {
            source_x = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            source_y = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            source_width = read_u32_at(box_ref.payload, &mut cursor, offset)?;
            source_height = read_u32_at(box_ref.payload, &mut cursor, offset)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(source_x == if have_source_region { crate::specs::part2_composition_word_at(box_ref.payload@, source_start) } else { 0 });
            assert(source_y == if have_source_region { crate::specs::part2_composition_word_at(box_ref.payload@, source_start + 4) } else { 0 });
            assert(source_width == if have_source_region { crate::specs::part2_composition_word_at(box_ref.payload@, source_start + 8) } else { 0 });
            assert(source_height == if have_source_region { crate::specs::part2_composition_word_at(box_ref.payload@, source_start + 12) } else { 0 });
            assert(cursor == record_end);
            assert(crate::specs::part2_instruction_record(super::box_reference_view(box_ref),
                composition, offset, flags, tick, position as nat) ==
                if target_width == 0 || target_height == 0
                    || (have_source_region && (source_width == 0 || source_height == 0)) {
                    Err(DecodeError::MalformedInput {offset, kind: MalformedKind::InvalidImageGeometry})
                } else if life_value as nat * tick as nat > u32::MAX as nat {
                    Err(crate::specs::part2_palette_arithmetic_error(offset))
                } else {
                    Ok(CompositionInstruction {
                        target_x, target_y, target_width, target_height,
                        life: (life_value as nat * tick as nat) as u32, persistent, next_reuse,
                        source_x, source_y, source_width, source_height,
                    })
                }) by {
                reveal(crate::specs::part2_instruction_record);
            }
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
        let life = life_value.checked_mul(tick).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(offset),
                ))]
            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
        )?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_instruction_record(super::box_reference_view(box_ref),
                composition, offset, flags, tick, position as nat) == Ok(CompositionInstruction {
                    target_x, target_y, target_width, target_height, life, persistent, next_reuse,
                    source_x, source_y, source_width, source_height,
                }));
        }
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
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_instruction_records); }
    Ok(CompositionInstructionSet {
        flags,
        repeat,
        tick,
        instructions,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(position)) == crate::specs::part2_read_composition_word(input@, *old(position), offset),
))]
pub(super) fn read_u32_at(
    input: &[u8],
    position: &mut usize,
    offset: u64,
) -> Result<u32, DecodeError> {
    let end = position.checked_add(4).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_palette_arithmetic_error(offset),
            ))]
        || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
    )?;
    let bytes = input
        .get(*position..end)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::InvalidBoxLength }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::InvalidBoxLength),
        )?;
    *position = end;
    Ok(read_u32([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_composition_storage_result(
        super::box_reference_view(box_ref),*limits,super::raw_composition_outcome(result)),
    super::raw_composition_outcome(result) != Err(DecodeError::AllocationFailed) ==> super::raw_composition_outcome(result)
        == crate::specs::part2_parse_composition(super::box_reference_view(box_ref), *limits),
))]
pub(super) fn parse_composition(
    box_ref: BoxRef<'_>,
    limits: &ResourceLimits,
) -> Result<Composition, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_composition_storage_normal(super::box_reference_view(box_ref),*limits);}
    let base_offset = box_ref.header.payload_offset()?;
    let mut reader = box_reader_from_input(box_ref.payload, limits)?;
    let mut options = None;
    let mut instruction_sets = Vec::new();
    let mut has_unknown_boxes = false;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_parse_composition(
    super::box_reference_view(box_ref), *limits); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost machine=crate::specs::part2_composition_storage_machine(box_ref.payload@,*limits,base_offset);
        let ghost root=|events:Seq<crate::specs::Part2JpipSnapshotEvent>|crate::specs::part2_composition_storage_run(
            super::box_reference_view(box_ref),*limits,events);
        let ghost mut storage_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(super::raw_instruction_sets_view(instruction_sets@) =~= Seq::<crate::specs::Part2RawInstructionSet>::empty());
        crate::specs::part2_composition_storage_machine_valid(box_ref.payload@,*limits,base_offset);
        assert forall|tail:Seq<crate::specs::Part2JpipSnapshotEvent>|root(storage_prefix+tail)
            ==crate::specs::part2_header_storage_boxes_run(machine,super::box_reader_state(&reader),
                (options,super::raw_instruction_sets_view(instruction_sets@),has_unknown_boxes),tail) by {
            assert(storage_prefix+tail =~= tail);
        }
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant_except_break expected == crate::specs::part2_composition_boxes(
                box_ref.payload@, super::box_reader_state(&reader), options,
                super::raw_instruction_sets_view(instruction_sets@), has_unknown_boxes, *limits, base_offset),
                expected == crate::specs::part2_parse_composition(super::box_reference_view(box_ref), *limits),
                crate::specs::part2_composition_storage_result(super::box_reference_view(box_ref),*limits,expected),
                machine==crate::specs::part2_composition_storage_machine(box_ref.payload@,*limits,base_offset),
                root==(|events:Seq<crate::specs::Part2JpipSnapshotEvent>|crate::specs::part2_composition_storage_run(
                    super::box_reference_view(box_ref),*limits,events)),
                crate::specs::part2_header_storage_machine_valid(machine),
                crate::specs::part2_cold_phase(root,storage_prefix,|events|crate::specs::part2_header_storage_boxes_run(
                    machine,super::box_reader_state(&reader),
                    (options,super::raw_instruction_sets_view(instruction_sets@),has_unknown_boxes),events)),
            ensures expected == crate::specs::part2_composition_finish(
                options, super::raw_instruction_sets_view(instruction_sets@), has_unknown_boxes, base_offset),
                crate::specs::part2_composition_storage_result(super::box_reference_view(box_ref),*limits,expected),
            decreases box_ref.payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! {
            super::channel_storage_box_kinds_known();
            reveal(crate::specs::part2_composition_boxes);reveal(crate::specs::part2_composition_storage_step);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_reader=super::box_reader_state(&reader);
            let ghost previous_state=(options,super::raw_instruction_sets_view(instruction_sets@),has_unknown_boxes);
        }
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
        let child = next.map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
            ))]
            |error| rebase_error(error, base_offset),
        )?;
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
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost request=crate::specs::Part2InstructionRequestContext {
                    child:crate::specs::Part2InstructionStorageContext {
                        input:super::box_reference_view(child),composition:options.get_Some_0(),base:base_offset,limits:*limits},
                    before:super::raw_instruction_sets_view(instruction_sets@)};
            }
            let parsed = parse_instruction_set(
                child,
                options.ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_raw_header_missing(base_offset),
                    ))]
                    || DecodeError::malformed(base_offset, MalformedKind::MissingRequiredStructure),
                )?,
                base_offset,
                limits,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error)=parsed {
                    if error==DecodeError::AllocationFailed {
                        crate::specs::part2_header_storage_request_instruction_error(request,error);
                        crate::specs::part2_header_storage_root_error(root,storage_prefix,machine,previous_reader,previous_state,
                            super::box_reference_view(child),crate::specs::Part2HeaderStorageRequest::InstructionSet {context:request},error);
                        crate::specs::part2_composition_storage_observed(super::box_reference_view(box_ref),*limits,Err(error));
                    }
                }
            }
            let instruction_set = parsed?;
            let actual = instruction_sets.len().checked_add(1).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(base_offset),
                ))]
                || DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
            )?;
            if actual as u64 > u64::from(limits.maximum_layers()) {
                return Err(DecodeError::limit(
                    Resource::Layers,
                    u64::from(limits.maximum_layers()),
                    actual as u64,
                ));
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous = instruction_sets@; }
            let reserved = crate::allocation::reserve_additional(&mut instruction_sets, 1);
            #[cfg(verus_keep_ghost)]
            proof! {
                let append=crate::specs::Part2InstructionAppendContext {
                    request,parsed:super::raw_instruction_set_view(&instruction_set)};
                crate::specs::part2_instruction_append_capacity_observed(
                    append,crate::allocation::inspection_capacity_outcome(reserved));
                if let Err(error)=reserved {
                    crate::specs::part2_header_storage_request_instruction_append_error(append,error);
                    crate::specs::part2_header_storage_root_error(root,storage_prefix,machine,previous_reader,previous_state,
                        super::box_reference_view(child),crate::specs::Part2HeaderStorageRequest::InstructionSet {context:request},error);
                    crate::specs::part2_composition_storage_observed(super::box_reference_view(box_ref),*limits,Err(error));
                }
            }
            reserved?;
            instruction_sets.push(instruction_set);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(super::raw_instruction_sets_view(instruction_sets@) =~=
                    super::raw_instruction_sets_view(previous).push(super::raw_instruction_set_view(&instruction_sets@[instruction_sets@.len() - 1])));
            }
        } else {
            has_unknown_boxes = true;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            storage_prefix=crate::specs::part2_header_storage_root_advance(root,storage_prefix,machine,previous_reader,previous_state,
                super::box_reference_view(child),(options,super::raw_instruction_sets_view(instruction_sets@),has_unknown_boxes));
        }
    }
    let (width, height, encoded_loop_count) = options.ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_raw_header_missing(base_offset),
        ))]
        || DecodeError::malformed(base_offset, MalformedKind::MissingRequiredStructure),
    )?;
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_validate_composition_dimensions(width, height, limits, offset),
))]
pub(super) fn validate_dimensions(
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
    let pixels = u64::from(width).checked_mul(u64::from(height)).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_palette_arithmetic_error(offset),
            ))]
        || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
    )?;
    if pixels > limits.maximum_pixels() {
        return Err(DecodeError::limit(
            Resource::Pixels,
            limits.maximum_pixels(),
            pixels,
        ));
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_any_layer_registration(
        super::raw_compositing_layers_view(layers@), layers.len() as nat),
))]
fn has_explicit_registration(layers: &[CompositingLayer<'_>]) -> bool {
    let mut found = false;
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_any_layer_registration);
        reveal(super::raw_compositing_layer_view);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= layers.len(),
            found == crate::specs::part2_any_layer_registration(
                super::raw_compositing_layers_view(layers@), index as nat),
        decreases layers.len() - index,
    ))]
    while index < layers.len() {
        found = found || !layers[index].registrations.is_empty();
        index += 1;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_any_layer_registration); }
    }
    found
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_validate_layer_references(
        super::raw_compositing_layers_view(layers@), codestream_count),
))]
pub(super) fn validate_layer_references(
    layers: &[CompositingLayer<'_>],
    codestream_count: usize,
) -> Result<(), DecodeError> {
    let explicit_registration = has_explicit_registration(layers);
    let mut layer_index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_validate_layer_references(
    super::raw_compositing_layers_view(layers@), codestream_count); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant layer_index <= layers.len(),
                explicit_registration == crate::specs::part2_any_layer_registration(
                    super::raw_compositing_layers_view(layers@), layers.len() as nat),
                expected == crate::specs::part2_validate_layer_references(
                    super::raw_compositing_layers_view(layers@), codestream_count),
                expected == crate::specs::part2_layer_references(
                    super::raw_compositing_layers_view(layers@), codestream_count, layer_index as nat),
            decreases layers.len() - layer_index,
        )
    )]
    while layer_index < layers.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_layer_references); }
        let layer = layers
            .get(layer_index)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        if layer.registrations.is_empty() {
            if explicit_registration || layer_index >= codestream_count {
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
                        layer_index < layers.len(),
                        layer == &layers@[layer_index as int],
                        expected == crate::specs::part2_validate_layer_references(
                            super::raw_compositing_layers_view(layers@), codestream_count),
                        expected == match crate::specs::part2_layer_registration_references(
                            super::raw_compositing_layer_view(layer), codestream_count, registration_index as nat) {
                            Err(error) => Err(error),
                            Ok(()) => crate::specs::part2_layer_references(
                                super::raw_compositing_layers_view(layers@), codestream_count, layer_index as nat + 1),
                        },
                    decreases layer.registrations.len() - registration_index,
                )
            )]
            while registration_index < layer.registrations.len() {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_layer_registration_references); }
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
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_layer_registration_references); }
        }
        layer_index = layer_index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_layer_references); }
    Ok(())
}
