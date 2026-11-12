use super::arithmetic::{
    arithmetic_overflow, decoded_signed_sample, decoded_unsigned_sample, invalid_image,
    validate_bytes,
};
use super::assembly::charge_assembly_bytes;
use super::{DecodedComponent, DecodedImage, TypedComponent, TypedImage, TypedSamples};
#[cfg(verus_keep_ghost)]
use super::{
    channel_definition_views, decoded_component_view, decoded_components_view, decoded_image_view,
    decoded_typed_components_view, decoded_typed_image_outcome, decoded_typed_samples_outcome,
    typed_component_definitions, typed_component_view, typed_image_definition_views,
};
use crate::codestream::ComponentInfo;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl DecodedImage {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == decoded_image_view(*self).0,))]
    pub const fn width(&self) -> u32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_image_view); }
        self.width
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == decoded_image_view(*self).1,))]
    pub const fn height(&self) -> u32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_image_view); }
        self.height
    }

    pub const fn x_origin(&self) -> u32 {
        self.x_origin
    }

    pub const fn y_origin(&self) -> u32 {
        self.y_origin
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures decoded_components_view(result@) == decoded_image_view(*self).4,
    ))]
    pub fn components(&self) -> &[DecodedComponent] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_image_view); }
        &self.components
    }

    pub fn component(&self, index: u16) -> Result<&DecodedComponent, DecodeError> {
        self.components
            .get(usize::from(index))
            .ok_or_else(invalid_image)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures decoded_typed_image_outcome(result) == crate::specs::part1_decoded_image_typed(
            decoded_image_view(*self), crate::limits::resource_decoded_bytes_limit(limits),
        ),
    ))]
    pub fn typed(&self, limits: &ResourceLimits) -> Result<TypedImage, DecodeError> {
        let mut components = Vec::with_capacity(self.components.len());
        let mut decoded_bytes = 0_u64;
        let mut index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_decoded_typed_components_empty(
                decoded_components_view(self.components@), crate::limits::resource_decoded_bytes_limit(limits),
            );
            assert(decoded_typed_components_view(components@) =~= Seq::empty());
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.components.len(),
                components.len() == index,
                crate::specs::part1_decoded_typed_components(
                    decoded_components_view(self.components@), crate::limits::resource_decoded_bytes_limit(limits), index as nat,
                ) == Ok((decoded_typed_components_view(components@), decoded_bytes)),
                forall |i: int| 0 <= i < components.len() ==> typed_component_definitions(&components@[i]).len() == 0,
                decreases self.components.len() - index,
            )
        )]
        while index < self.components.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_decoded_typed_components_step(
                    decoded_components_view(self.components@), crate::limits::resource_decoded_bytes_limit(limits), index as nat,
                );
            }
            let component = self.components.get(index).ok_or_else(invalid_image)?;
            match charge_assembly_bytes(
                component.samples.len(),
                &mut decoded_bytes,
                limits.maximum_decoded_bytes(),
            ) {
                Ok(()) => {}
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_decoded_typed_components_error(
                            decoded_components_view(self.components@), crate::limits::resource_decoded_bytes_limit(limits),
                            index as nat + 1, self.components.len() as nat, error,
                        );
                    }
                    return Err(error);
                }
            }
            let samples = match component.typed_samples(limits) {
                Ok(samples) => samples,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_decoded_typed_components_error(
                            decoded_components_view(self.components@), crate::limits::resource_decoded_bytes_limit(limits),
                            index as nat + 1, self.components.len() as nat, error,
                        );
                    }
                    return Err(error);
                }
            };
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = components@; }
            components.push(TypedComponent {
                width: component.width,
                height: component.height,
                info: component.info,
                samples,
                channel_definitions: Vec::new(),
            });
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(decoded_typed_components_view(components@) =~= decoded_typed_components_view(before).push(
                    typed_component_view(&components@[index as int]),
                ));
                assert forall |i: int| 0 <= i < components.len() implies
                    typed_component_definitions(&components@[i]).len() == 0 by {};
            }
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        let image = TypedImage {
            width: self.width,
            height: self.height,
            x_origin: self.x_origin,
            y_origin: self.y_origin,
            components,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |i: int| 0 <= i < image.components.len() implies
                typed_image_definition_views(&image)[i] == Seq::empty() by {
                assert(typed_component_definitions(&image.components@[i]).len() == 0);
                assert(channel_definition_views(typed_component_definitions(&image.components@[i])) =~= Seq::empty());
            }
            assert(typed_image_definition_views(&image) =~= Seq::new(image.components.len() as nat, |i: int| Seq::empty()));
        }
        Ok(image)
    }
}

impl DecodedComponent {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == decoded_component_view(*self).0,))]
    pub const fn width(&self) -> u32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_component_view); }
        self.width
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == decoded_component_view(*self).1,))]
    pub const fn height(&self) -> u32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_component_view); }
        self.height
    }

    pub const fn info(&self) -> ComponentInfo {
        self.info
    }

    pub const fn fraction_bits(&self) -> u8 {
        self.fraction_bits
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == decoded_component_view(*self).4,
    ))]
    pub fn samples(&self) -> &[i64] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_component_view); }
        &self.samples
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures decoded_typed_samples_outcome(result) == crate::specs::part1_decoded_component_typed_samples(
            decoded_component_view(*self), crate::limits::resource_decoded_bytes_limit(limits),
        ),
    ))]
    pub fn typed_samples(&self, limits: &ResourceLimits) -> Result<TypedSamples, DecodeError> {
        if self.info.precision == 0 || self.info.precision > 38 {
            return Err(invalid_image());
        }
        validate_bytes(self.samples.len(), 8, limits)?;
        let precision = self.info.precision;
        let shift = self
            .info
            .precision
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
        let signed_power = 1_i64 << u32::from(shift);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(signed_power > 0) by(bit_vector)
                requires shift <= 37, signed_power == 1i64 << (shift as u32);
        }
        let signed_min = 0_i64
            .checked_sub(signed_power)
            .ok_or_else(arithmetic_overflow)?;
        let signed_max = signed_power
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
        let unsigned_power = 1_u64 << u32::from(precision);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(unsigned_power > 0) by(bit_vector)
                requires precision <= 38,
                    unsigned_power == 1u64 << (precision as u32);
        }
        let unsigned_max = unsigned_power
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
        if self.info.signed {
            let mut output = Vec::with_capacity(self.samples.len());
            let mut index = 0;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_decoded_signed_empty(
                    self.samples@, self.fraction_bits, self.info.precision,
                );
            }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant index <= self.samples.len(),
                    0 < self.info.precision <= 38,
                    self.info.signed,
                    signed_min == crate::specs::part1_output_minimum(self.info.precision, true),
                    signed_max == crate::specs::part1_output_maximum(self.info.precision, true),
                    crate::specs::part1_image_byte_budget(
                        self.samples.len() as nat, 8, crate::limits::resource_decoded_bytes_limit(limits),
                    ) == Ok(()),
                    crate::specs::part1_decoded_signed_prefix(
                        self.samples@, self.fraction_bits, self.info.precision, index as nat,
                    ) == Ok(output@),
                    decreases self.samples.len() - index,
                )
            )]
            while index < self.samples.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_decoded_signed_step(
                        self.samples@, self.fraction_bits, self.info.precision, index as nat,
                    );
                }
                let value = match decoded_signed_sample(
                    self.samples[index],
                    self.fraction_bits,
                    signed_min,
                    signed_max,
                ) {
                    Ok(value) => value,
                    Err(error) => {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::proofs::production_impl::production_decoded_signed_error(
                                self.samples@, self.fraction_bits, self.info.precision, index as nat + 1, self.samples.len() as nat, error,
                            );
                        }
                        return Err(error);
                    }
                };
                output.push(value);
                index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            Ok(TypedSamples::Signed(output))
        } else {
            let level_shift = 1_i64 << u32::from(shift);
            let mut output = Vec::with_capacity(self.samples.len());
            let mut index = 0;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_decoded_unsigned_empty(
                    self.samples@, self.fraction_bits, self.info.precision,
                );
            }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant index <= self.samples.len(),
                    0 < self.info.precision <= 38,
                    !self.info.signed,
                    level_shift == 1i64 << ((self.info.precision - 1) as u8),
                    unsigned_max == (1u64 << self.info.precision) - 1,
                    crate::specs::part1_image_byte_budget(
                        self.samples.len() as nat, 8, crate::limits::resource_decoded_bytes_limit(limits),
                    ) == Ok(()),
                    crate::specs::part1_decoded_unsigned_prefix(
                        self.samples@, self.fraction_bits, self.info.precision, index as nat,
                    ) == Ok(output@),
                    decreases self.samples.len() - index,
                )
            )]
            while index < self.samples.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_decoded_unsigned_step(
                        self.samples@, self.fraction_bits, self.info.precision, index as nat,
                    );
                }
                let value = match decoded_unsigned_sample(
                    self.samples[index],
                    self.fraction_bits,
                    level_shift,
                    unsigned_max,
                ) {
                    Ok(value) => value,
                    Err(error) => {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::proofs::production_impl::production_decoded_unsigned_error(
                                self.samples@, self.fraction_bits, self.info.precision, index as nat + 1, self.samples.len() as nat, error,
                            );
                        }
                        return Err(error);
                    }
                };
                output.push(value);
                index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            Ok(TypedSamples::Unsigned(output))
        }
    }
}
