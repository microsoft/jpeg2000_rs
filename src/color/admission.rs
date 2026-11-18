use super::ChannelLayout;
#[cfg(verus_keep_ghost)]
use super::channel_layout_result;
use super::geometry::{
    arithmetic_overflow, checked_area, invalid_channel_layout, invalid_color_input,
    registered_ceil_div,
};
use crate::image::{ChannelAssociation, ChannelType, TypedComponent, TypedImage, TypedSamples};
use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::specs::part2_color_layout_storage_result(crate::image::typed_image_definition_views(image),color_count,
            channel_layout_result(result)),
        result!=Err(DecodeError::AllocationFailed) ==> channel_layout_result(result) == crate::specs::color_channel_layout(
            crate::image::typed_image_definition_views(image), color_count,
        ),
    )
)]
pub(super) fn channel_layout(
    image: &TypedImage,
    color_count: usize,
) -> Result<ChannelLayout, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input_definitions = crate::image::typed_image_definition_views(image); }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_color_layout_storage_normal(input_definitions,color_count);}
    let mut has_definitions = false;
    let component_count = image.components().len();
    let mut component_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component_index <= component_count,
                crate::specs::part2_color_layout_storage_result(input_definitions,color_count,
                    crate::specs::color_channel_layout(input_definitions,color_count)),
                input_definitions == crate::image::typed_image_definition_views(image),
                component_count == input_definitions.len(),
                has_definitions == (exists|i: int| #![trigger input_definitions[i]]
                    0 <= i < component_index && input_definitions[i].len() > 0),
            decreases component_count - component_index,
        )
    )]
    while component_index < component_count {
        let component = image
            .components()
            .get(component_index)
            .ok_or_else(invalid_color_input)?;
        let definitions = component.channel_definitions();
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(input_definitions[component_index as int].len() == definitions.len());
            crate::proofs::production_impl::production_color_definition_presence_step(
                input_definitions, component_index as nat,
            );
        }
        if !definitions.is_empty() {
            has_definitions = true;
        }
        component_index = component_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    if !has_definitions {
        if component_count != color_count {
            return Err(invalid_channel_layout());
        }
        let allocated = if color_count == 0 {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(color_count)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let request=crate::specs::Part2ColorOutputCapacity::LayoutColors {definitions:input_definitions,colors:color_count};
            crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
            if let Err(error)=allocated {
                crate::specs::part2_color_layout_owner_present(input_definitions,color_count);
                crate::specs::part2_color_layout_storage_refused(input_definitions,color_count,request,error);
            }
        }
        let mut colors = allocated?;
        component_index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component_index <= color_count,
                    crate::specs::part2_color_layout_storage_result(input_definitions,color_count,
                        crate::specs::color_channel_layout(input_definitions,color_count)),
                    input_definitions == crate::image::typed_image_definition_views(image),
                    input_definitions.len() == color_count,
                    !(exists|i: int| #![trigger input_definitions[i]]
                        0 <= i < input_definitions.len() && input_definitions[i].len() > 0),
                    colors@ == Seq::new(component_index as nat, |i: int| i as usize),
                decreases color_count - component_index,
            )
        )]
        while component_index < color_count {
            colors.push(component_index);
            component_index = component_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        return Ok(ChannelLayout {
            colors,
            alphas: Vec::new(),
        });
    }

    let allocated = crate::allocation::filled_values(usize::MAX, color_count);
    #[cfg(verus_keep_ghost)]
    proof! {
        let request=crate::specs::Part2ColorOutputCapacity::LayoutColors {definitions:input_definitions,colors:color_count};
        crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(allocated));
        if let Err(error)=allocated {
            crate::specs::part2_color_layout_owner_present(input_definitions,color_count);
            crate::specs::part2_color_layout_storage_refused(input_definitions,color_count,request,error);
        }
    }
    let mut colors = allocated?;
    let mut alphas = Vec::new();
    component_index = 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_color_layout_empty(input_definitions, color_count);
        assert(colors@ =~= Seq::new(color_count as nat, |i: int| usize::MAX));
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component_index <= component_count,
                crate::specs::part2_color_layout_storage_result(input_definitions,color_count,
                    crate::specs::color_channel_layout(input_definitions,color_count)),
                input_definitions == crate::image::typed_image_definition_views(image),
                component_count == input_definitions.len(),
                colors.len() == color_count,
                exists|i: int| #![trigger input_definitions[i]]
                    0 <= i < input_definitions.len() && input_definitions[i].len() > 0,
                crate::specs::color_layout_components_prefix(input_definitions, color_count, component_index as nat)
                    == Ok((colors@, alphas@)),
            decreases component_count - component_index,
        )
    )]
    while component_index < component_count {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = (colors@, alphas@); }
        let component = image
            .components()
            .get(component_index)
            .ok_or_else(invalid_color_input)?;
        let definitions = component.channel_definitions();
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost current_definitions = crate::image::channel_definition_views(definitions@); }
        let mut definition_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_layout_step(input_definitions, color_count, component_index as nat);
            crate::proofs::production_impl::production_color_definitions_empty(initial, current_definitions, component_index, color_count);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant definition_index <= definitions.len(),
                    crate::specs::part2_color_layout_storage_result(input_definitions,color_count,
                        crate::specs::color_channel_layout(input_definitions,color_count)),
                    input_definitions == crate::image::typed_image_definition_views(image),
                    component_index < component_count && component_count == input_definitions.len(),
                    current_definitions == crate::image::channel_definition_views(definitions@),
                    current_definitions == input_definitions[component_index as int],
                    colors.len() == color_count,
                    exists|i: int| #![trigger input_definitions[i]]
                        0 <= i < input_definitions.len() && input_definitions[i].len() > 0,
                    crate::specs::color_layout_components_prefix(input_definitions, color_count, component_index as nat) == Ok(initial),
                    crate::specs::color_layout_components_prefix(input_definitions, color_count, component_index as nat + 1)
                        == crate::specs::color_layout_definitions_prefix(
                            initial, current_definitions, component_index, color_count, current_definitions.len(),
                        ),
                    crate::specs::color_layout_definitions_prefix(initial, current_definitions,
                        component_index, color_count, definition_index as nat) == Ok((colors@, alphas@)),
                decreases definitions.len() - definition_index,
            )
        )]
        while definition_index < definitions.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_color_definitions_step(
                    initial, current_definitions, component_index, color_count, definition_index as nat,
                );
            }
            let definition = *definitions
                .get(definition_index)
                .ok_or_else(invalid_color_input)?;
            match definition.channel_type() {
                ChannelType::Color => {
                    let association = match definition.association() {
                        ChannelAssociation::Color(value) => value,
                        _ => {
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                crate::proofs::production_impl::production_color_definitions_error(
                                    initial, current_definitions, component_index, color_count, definition_index as nat + 1,
                                    current_definitions.len(), crate::specs::color_layout_error(),
                                );
                                crate::proofs::production_impl::production_color_layout_error(
                                    input_definitions, color_count, component_index as nat + 1,
                                    input_definitions.len(), crate::specs::color_layout_error(),
                                );
                            }
                            return Err(invalid_channel_layout());
                        }
                    };
                    if association == 0 || usize::from(association) > color_count {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::proofs::production_impl::production_color_definitions_error(
                                initial, current_definitions, component_index, color_count, definition_index as nat + 1,
                                current_definitions.len(), crate::specs::color_layout_error(),
                            );
                            crate::proofs::production_impl::production_color_layout_error(
                                input_definitions, color_count, component_index as nat + 1,
                                input_definitions.len(), crate::specs::color_layout_error(),
                            );
                        }
                        return Err(invalid_channel_layout());
                    }
                    let slot_index = usize::from(association - 1);
                    if colors[slot_index] != usize::MAX && colors[slot_index] != component_index {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::proofs::production_impl::production_color_definitions_error(
                                initial, current_definitions, component_index, color_count, definition_index as nat + 1,
                                current_definitions.len(), crate::specs::color_layout_error(),
                            );
                            crate::proofs::production_impl::production_color_layout_error(
                                input_definitions, color_count, component_index as nat + 1,
                                input_definitions.len(), crate::specs::color_layout_error(),
                            );
                        }
                        return Err(invalid_channel_layout());
                    }
                    *colors.get_mut(slot_index).ok_or_else(invalid_color_input)? = component_index;
                }
                ChannelType::Opacity | ChannelType::PremultipliedOpacity => {
                    match validate_alpha_association(definition.association(), color_count) {
                        Ok(()) => {}
                        Err(error) => {
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                crate::proofs::production_impl::production_color_definitions_error(
                                    initial, current_definitions, component_index, color_count, definition_index as nat + 1,
                                    current_definitions.len(), error,
                                );
                                crate::proofs::production_impl::production_color_layout_error(
                                    input_definitions, color_count, component_index as nat + 1,
                                    input_definitions.len(), error,
                                );
                            }
                            return Err(error);
                        }
                    }
                    let reserved = crate::allocation::reserve_additional(&mut alphas, 1);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(crate::specs::part2_color_layout_alpha_admitted(input_definitions,color_count,component_index as nat,definition_index as nat));
                        let request=crate::specs::Part2ColorOutputCapacity::LayoutAlpha {definitions:input_definitions,colors:color_count,
                            component:component_index as nat,record:definition_index as nat};
                        crate::specs::part2_color_output_capacity_observed(request,crate::allocation::inspection_capacity_outcome(reserved));
                        if let Err(error)=reserved {
                            crate::specs::part2_color_layout_alpha_present(input_definitions,color_count,component_index as nat,definition_index as nat);
                            crate::specs::part2_color_layout_storage_refused(input_definitions,color_count,request,error);
                        }
                    }
                    reserved?;
                    alphas.push((
                        component_index,
                        matches!(definition.channel_type(), ChannelType::PremultipliedOpacity),
                        definition.association(),
                    ));
                }
                ChannelType::Unspecified => {
                    // Unspecified channels are intentionally not part of colour conversion.
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::color_layout_definitions_prefix(initial, current_definitions,
                    component_index, color_count, definition_index as nat + 1) == Ok((colors@, alphas@)));
            }
            definition_index = definition_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        component_index = component_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost complete = (colors@, alphas@); }
    component_index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component_index <= colors.len(),
                crate::specs::part2_color_layout_storage_result(input_definitions,color_count,
                    crate::specs::color_channel_layout(input_definitions,color_count)),
                input_definitions == crate::image::typed_image_definition_views(image),
                complete == (colors@, alphas@),
                exists|i: int| #![trigger input_definitions[i]]
                    0 <= i < input_definitions.len() && input_definitions[i].len() > 0,
                crate::specs::color_layout_components_prefix(input_definitions, color_count, input_definitions.len()) == Ok(complete),
                forall|i: int| #![trigger complete.0[i]] 0 <= i < component_index ==> complete.0[i] != usize::MAX,
            decreases colors.len() - component_index,
        )
    )]
    while component_index < colors.len() {
        if *colors
            .get(component_index)
            .ok_or_else(invalid_color_input)?
            == usize::MAX
        {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(complete.0[component_index as int] == usize::MAX);
                assert(exists|i: int| #![trigger complete.0[i]]
                    0 <= i < complete.0.len() && complete.0[i] == usize::MAX);
            }
            return Err(invalid_channel_layout());
        }
        component_index = component_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    Ok(ChannelLayout { colors, alphas })
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_alpha_association(association, color_count),)
)]
fn validate_alpha_association(
    association: ChannelAssociation,
    color_count: usize,
) -> Result<(), DecodeError> {
    match association {
        ChannelAssociation::Color(value) if value == 0 || usize::from(value) > color_count => {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidAlphaAssociation,
            });
        }
        _ => {}
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_validate_components(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image), (layout.colors@, layout.alphas@),
        ),
    )
)]
pub(super) fn validate_components(
    image: &TypedImage,
    layout: &ChannelLayout,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost components = crate::image::typed_image_component_views(image);
        let ghost geometry = crate::image::typed_image_geometry(image);
        let ghost colors = layout.colors@;
        let ghost alphas = Seq::new(layout.alphas@.len(), |i: int| layout.alphas@[i].0);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_color_validation_empty(components, geometry, colors);
        crate::proofs::production_impl::production_color_validation_empty(components, geometry, alphas);
    }
    let mut color_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant color_index <= layout.colors.len(),
                components == crate::image::typed_image_component_views(image),
                geometry == crate::image::typed_image_geometry(image),
                colors == layout.colors@,
                alphas == Seq::new(layout.alphas@.len(), |i: int| layout.alphas@[i].0),
                crate::specs::color_validate_indices_prefix(components, geometry, colors, color_index as nat) == Ok(()),
            decreases layout.colors.len() - color_index,
        )
    )]
    while color_index < layout.colors.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_validation_step(components, geometry, colors, color_index as nat);
        }
        let component_index = *layout
            .colors
            .get(color_index)
            .ok_or_else(invalid_color_input)?;
        let status = validate_component_index(image, component_index);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = status {
                crate::proofs::production_impl::production_color_validation_error(
                    components, geometry, colors, color_index as nat + 1, colors.len(), error,
                );
            }
        }
        status?;
        color_index = color_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let mut alpha_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant alpha_index <= layout.alphas.len(),
                components == crate::image::typed_image_component_views(image),
                geometry == crate::image::typed_image_geometry(image),
                colors == layout.colors@,
                alphas == Seq::new(layout.alphas@.len(), |i: int| layout.alphas@[i].0),
                crate::specs::color_validate_indices_prefix(components, geometry, colors, colors.len()) == Ok(()),
                crate::specs::color_validate_indices_prefix(components, geometry, alphas, alpha_index as nat) == Ok(()),
            decreases layout.alphas.len() - alpha_index,
        )
    )]
    while alpha_index < layout.alphas.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_validation_step(components, geometry, alphas, alpha_index as nat);
        }
        let component_index = layout
            .alphas
            .get(alpha_index)
            .ok_or_else(invalid_color_input)?
            .0;
        let status = validate_component_index(image, component_index);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = status {
                crate::proofs::production_impl::production_color_validation_error(
                    components, geometry, alphas, alpha_index as nat + 1, alphas.len(), error,
                );
            }
        }
        status?;
        alpha_index = alpha_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_validate_component_index(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image), index,
        ),
    )
)]
fn validate_component_index(image: &TypedImage, index: usize) -> Result<(), DecodeError> {
    let component = image
        .components()
        .get(index)
        .ok_or_else(invalid_color_input)?;
    validate_component(component, image)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_validate_component(
            crate::image::typed_component_view(component), crate::image::typed_image_geometry(image),
        ),
    )
)]
fn validate_component(component: &TypedComponent, image: &TypedImage) -> Result<(), DecodeError> {
    let info = component.info();
    if info.precision == 0 || info.precision > 38 {
        return Err(invalid_color_input());
    }
    if info.signed != matches!(component.samples(), TypedSamples::Signed(_)) {
        return Err(invalid_color_input());
    }
    if info.x_subsampling == 0 || info.y_subsampling == 0 {
        return Err(invalid_color_input());
    }
    let image_x1 = image
        .x_origin()
        .checked_add(image.width())
        .ok_or_else(arithmetic_overflow)?;
    let image_y1 = image
        .y_origin()
        .checked_add(image.height())
        .ok_or_else(arithmetic_overflow)?;
    let expected_width =
        registered_ceil_div(image_x1, u32::from(info.x_subsampling), info.x_registration)?
            .checked_sub(registered_ceil_div(
                image.x_origin(),
                u32::from(info.x_subsampling),
                info.x_registration,
            )?)
            .ok_or_else(arithmetic_overflow)?;
    let expected_height =
        registered_ceil_div(image_y1, u32::from(info.y_subsampling), info.y_registration)?
            .checked_sub(registered_ceil_div(
                image.y_origin(),
                u32::from(info.y_subsampling),
                info.y_registration,
            )?)
            .ok_or_else(arithmetic_overflow)?;
    if component.width() != expected_width || component.height() != expected_height {
        return Err(invalid_color_input());
    }
    let expected_samples = checked_area(expected_width, expected_height)?;
    let actual_samples = match component.samples() {
        TypedSamples::Signed(samples) => samples.len(),
        TypedSamples::Unsigned(samples) => samples.len(),
    };
    if actual_samples != expected_samples {
        return Err(invalid_color_input());
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_validate_output_size(
            crate::image::typed_image_geometry(image).0, crate::image::typed_image_geometry(image).1,
            color_count, alpha_count, crate::limits::resource_decoded_bytes_limit(limits),
            crate::limits::resource_work_limit(limits),
        ),
    )
)]
pub(super) fn validate_output_size(
    image: &TypedImage,
    color_count: usize,
    alpha_count: usize,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    let channels = color_count
        .checked_add(alpha_count)
        .ok_or_else(arithmetic_overflow)?;
    let samples = checked_area(image.width(), image.height())?
        .checked_mul(channels)
        .ok_or_else(arithmetic_overflow)?;
    let bytes = (samples as u64)
        .checked_mul(2)
        .ok_or_else(arithmetic_overflow)?;
    if bytes > limits.maximum_decoded_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: limits.maximum_decoded_bytes(),
            actual: bytes,
        });
    }
    let work = u64::try_from(samples).map_err(|_| arithmetic_overflow())?;
    if work > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: work,
        });
    }
    Ok(())
}
