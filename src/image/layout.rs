use super::arithmetic::{arithmetic_overflow, checked_area, invalid_image};
use super::{
    ChannelAssociation, ChannelDefinition, ChannelType, TypedComponent, TypedImage, TypedSamples,
};
#[cfg(verus_keep_ghost)]
use super::{
    channel_definition_view, channel_definition_views, decoded_typed_components_view,
    decoded_typed_image_outcome, typed_component_definitions, typed_component_output_view,
    typed_component_reference_output, typed_component_value_view, typed_component_view,
    typed_components_output_view, typed_image_components, typed_image_geometry, typed_samples_view,
};
use crate::codestream::ComponentInfo;
use crate::{DecodeError, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl TypedImage {
    #[cfg(test)]
    pub(crate) fn from_components(
        width: u32,
        height: u32,
        components: Vec<TypedComponent>,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        Self::from_components_with_origin(width, height, 0, 0, components, limits)
    }

    #[cfg(test)]
    pub(crate) fn from_components_with_origin(
        width: u32,
        height: u32,
        x_origin: u32,
        y_origin: u32,
        components: Vec<TypedComponent>,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        typed_image_from_components_with_origin(
            width, height, x_origin, y_origin, components, limits,
        )
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures decoded_typed_image_outcome(result) == crate::specs::part2_typed_image_from_parts(
            width, height, x_origin, y_origin, typed_components_output_view(components@),
            crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),
        ),
    ))]
pub(crate) fn typed_image_from_components_with_origin(
    width: u32,
    height: u32,
    x_origin: u32,
    y_origin: u32,
    components: Vec<TypedComponent>,
    limits: &ResourceLimits,
) -> Result<TypedImage, DecodeError> {
    x_origin
        .checked_add(width)
        .ok_or_else(arithmetic_overflow)?;
    y_origin
        .checked_add(height)
        .ok_or_else(arithmetic_overflow)?;
    let component_count = match u16::try_from(components.len()) {
        Ok(count) => count,
        Err(_) => return Err(arithmetic_overflow()),
    };
    if component_count > limits.maximum_components() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Components,
            limit: u64::from(limits.maximum_components()),
            actual: components.len() as u64,
        });
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_typed_image_admission_empty(typed_components_output_view(components@), crate::limits::resource_decoded_bytes_limit(limits));
    }
    let mut decoded_bytes = 0_u64;
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= components.len(),
            x_origin as nat + width as nat <= u32::MAX,
            y_origin as nat + height as nat <= u32::MAX,
            components.len() <= u16::MAX,
            components.len() <= crate::limits::resource_component_limit(limits),
            crate::specs::part2_typed_image_admission_prefix(
                typed_components_output_view(components@), crate::limits::resource_decoded_bytes_limit(limits), index as nat,
            ) == Ok(decoded_bytes),
            decreases components.len() - index,
        ))]
    while index < components.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_typed_image_admission_step(typed_components_output_view(components@), crate::limits::resource_decoded_bytes_limit(limits), index as nat);
            crate::proofs::production_impl::production_typed_image_admission_error(typed_components_output_view(components@), crate::limits::resource_decoded_bytes_limit(limits), index as nat + 1, components.len() as nat);
        }
        let component = components.get(index).ok_or_else(invalid_image)?;
        let sample_count = match &component.samples {
            TypedSamples::Signed(samples) => samples.len(),
            TypedSamples::Unsigned(samples) => samples.len(),
        };
        let expected_samples = checked_area(component.width, component.height)?;
        if sample_count != expected_samples {
            return Err(invalid_image());
        }
        decoded_bytes = decoded_bytes
            .checked_add(
                (sample_count as u64)
                    .checked_mul(8)
                    .ok_or_else(arithmetic_overflow)?,
            )
            .ok_or_else(arithmetic_overflow)?;
        if decoded_bytes > limits.maximum_decoded_bytes() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::DecodedBytes,
                limit: limits.maximum_decoded_bytes(),
                actual: decoded_bytes,
            });
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(Seq::new(components@.len(), |i: int| typed_components_output_view(components@)[i].0) =~= decoded_typed_components_view(components@));
        assert(Seq::new(components@.len(), |i: int| typed_components_output_view(components@)[i].1) =~= Seq::new(components@.len(), |i: int| channel_definition_views(typed_component_definitions(&components@[i]))));
    }
    Ok(TypedImage {
        width,
        height,
        x_origin,
        y_origin,
        components,
    })
}

impl TypedImage {
    #[cfg(test)]
    pub(crate) fn for_test(
        width: u32,
        height: u32,
        x_origin: u32,
        y_origin: u32,
        components: Vec<TypedComponent>,
    ) -> Self {
        Self {
            width,
            height,
            x_origin,
            y_origin,
            components,
        }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == typed_image_geometry(self).0,)
    )]
    pub const fn width(&self) -> u32 {
        self.width
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == typed_image_geometry(self).1,)
    )]
    pub const fn height(&self) -> u32 {
        self.height
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == typed_image_geometry(self).2,)
    )]
    pub const fn x_origin(&self) -> u32 {
        self.x_origin
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == typed_image_geometry(self).3,)
    )]
    pub const fn y_origin(&self) -> u32 {
        self.y_origin
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(components => ensures components@ == typed_image_components(self),)
    )]
    pub fn components(&self) -> &[TypedComponent] {
        &self.components
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures typed_component_reference_output(result) == crate::specs::part2_typed_image_component(
            typed_components_output_view(typed_image_components(self)), index,
        ),
    ))]
    pub fn component(&self, index: u16) -> Result<&TypedComponent, DecodeError> {
        match self.components.get(usize::from(index)) {
            Some(component) => Ok(component),
            None => Err(invalid_image()),
        }
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(component =>
        ensures typed_component_value_view(component) == crate::specs::part2_typed_component_from_parts(
            width, height, info, typed_samples_view(&samples),
        ),
        typed_component_output_view(&component) == crate::specs::part2_typed_component_from_parts(
            width, height, info, typed_samples_view(&samples),
        ),
        typed_component_definitions(&component) == Seq::<ChannelDefinition>::empty(),
    )
)]
pub(crate) fn typed_component_from_parts(
    width: u32,
    height: u32,
    info: ComponentInfo,
    samples: TypedSamples,
) -> TypedComponent {
    TypedComponent {
        width,
        height,
        info,
        samples,
        channel_definitions: Vec::new(),
    }
}

impl TypedComponent {
    #[cfg(test)]
    pub(crate) fn from_parts(
        width: u32,
        height: u32,
        info: ComponentInfo,
        samples: TypedSamples,
    ) -> Self {
        typed_component_from_parts(width, height, info, samples)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            ensures typed_component_view(final(self)) == typed_component_view(old(self)),
            typed_component_definitions(final(self))
                == typed_component_definitions(old(self)).push(definition),
            typed_component_output_view(final(self))
                == (typed_component_output_view(old(self)).0,
                    typed_component_output_view(old(self)).1.push(channel_definition_view(definition))),
        )
    )]
    pub(crate) fn add_channel_definition(&mut self, definition: ChannelDefinition) {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = typed_component_output_view(self).1; }
        self.channel_definitions.push(definition);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(typed_component_output_view(self).1 =~= previous.push(channel_definition_view(definition)));
        }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            ensures typed_component_view(final(self)) == typed_component_view(old(self)),
            typed_component_definitions(final(self)) == Seq::<ChannelDefinition>::empty(),
        )
    )]
    pub(crate) fn clear_channel_definitions(&mut self) {
        self.channel_definitions.clear();
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == typed_component_view(self).width,)
    )]
    pub const fn width(&self) -> u32 {
        self.width
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == typed_component_view(self).height,)
    )]
    pub const fn height(&self) -> u32 {
        self.height
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == typed_component_view(self).info,)
    )]
    pub const fn info(&self) -> ComponentInfo {
        self.info
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures typed_samples_view(value) == typed_component_view(self).samples,)
    )]
    pub const fn samples(&self) -> &TypedSamples {
        &self.samples
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(definitions => ensures definitions@ == typed_component_definitions(self),)
    )]
    pub fn channel_definitions(&self) -> &[ChannelDefinition] {
        &self.channel_definitions
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures channel_definition_view(result) == (channel_type, association),
))]
pub(crate) const fn channel_definition_new(
    channel_type: ChannelType,
    association: ChannelAssociation,
) -> ChannelDefinition {
    ChannelDefinition {
        channel_type,
        association,
    }
}

impl ChannelDefinition {
    pub const fn new(channel_type: ChannelType, association: ChannelAssociation) -> Self {
        channel_definition_new(channel_type, association)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(kind => ensures kind == channel_definition_view(self).0,)
    )]
    pub const fn channel_type(self) -> ChannelType {
        self.channel_type
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(association => ensures association == channel_definition_view(self).1,)
    )]
    pub const fn association(self) -> ChannelAssociation {
        self.association
    }
}
