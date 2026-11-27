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

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == decoded_image_view(*self).2,))]
    pub const fn x_origin(&self) -> u32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_image_view); }
        self.x_origin
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == decoded_image_view(*self).3,))]
    pub const fn y_origin(&self) -> u32 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decoded_image_view); }
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
        ensures crate::specs::part2_typed_image_result(decoded_image_view(*self),crate::limits::resource_decoded_bytes_limit(limits),decoded_typed_image_outcome(result)),
        decoded_typed_image_outcome(result)!=Err(DecodeError::AllocationFailed) ==> decoded_typed_image_outcome(result) == crate::specs::part1_decoded_image_typed(
            decoded_image_view(*self), crate::limits::resource_decoded_bytes_limit(limits),
        ),
    ))]
    pub fn typed(&self, limits: &ResourceLimits) -> Result<TypedImage, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost source=decoded_image_view(*self);}
        #[cfg(verus_keep_ghost)]
        proof! {reveal(decoded_image_view);crate::specs::part2_typed_image_normal(source,crate::limits::resource_decoded_bytes_limit(limits));}
        let reserved = if self.components.is_empty() {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(self.components.len())
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let context=crate::specs::Part2TypedCapacityContext::Image {source,maximum:crate::limits::resource_decoded_bytes_limit(limits)};
            crate::specs::part2_typed_capacity_observed(context,crate::allocation::inspection_capacity_outcome(reserved));
            if reserved.is_err(){crate::specs::part2_typed_image_owner_refused(source,crate::limits::resource_decoded_bytes_limit(limits));}
        }
        let mut components = reserved?;
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
                source==decoded_image_view(*self),
                source.4==decoded_components_view(self.components@),
                crate::specs::part2_typed_image_result(source,crate::limits::resource_decoded_bytes_limit(limits),crate::specs::part1_decoded_image_typed(source,crate::limits::resource_decoded_bytes_limit(limits))),
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
            proof_decl! {let ghost prior=(decoded_typed_components_view(components@),decoded_bytes);}
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
                        crate::specs::part2_typed_image_component_error(source,crate::limits::resource_decoded_bytes_limit(limits),index as nat,prior,error);
                        if error!=DecodeError::AllocationFailed{crate::proofs::production_impl::production_decoded_typed_components_error(
                            decoded_components_view(self.components@), crate::limits::resource_decoded_bytes_limit(limits),
                            index as nat + 1, self.components.len() as nat, error,
                        );
                        }
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 0 < precision <= 38, fraction_bits <= 62,
        level_shift == 1i64 << ((precision - 1) as u8),
        maximum == (1u64 << precision) - 1,
        samples.len() == 64,
        old(output).len() + 64 <= usize::MAX,
        ({
            let bound: int = if fraction_bits == 0 {
                i64::MAX as int - level_shift as int
            } else {
                i64::MAX as int - (1i64 << ((fraction_bits - 1) as u32)) as int
            };
            forall |k: int| 0 <= k < 64 ==> #[trigger] samples@[k] <= bound
        }),
    ensures final(output).len() == old(output).len() + 64,
        final(output)@.subrange(0, old(output).len() as int) == old(output)@,
        forall |k: int| 0 <= k < 64 ==>
            crate::specs::part1_decoded_unsigned_value(samples@[k], fraction_bits, level_shift, maximum)
                == Ok(#[trigger] final(output)@[old(output).len() as int + k]),
))]
#[inline]
fn append_typed_unsigned_chunk(
    samples: &[i64],
    output: &mut Vec<u64>,
    fraction_bits: u8,
    level_shift: i64,
    maximum: u64,
    #[cfg(verus_keep_ghost)] precision: Ghost<u8>,
) {
    let mut chunk = [0_u64; 64];
    if fraction_bits == 0 {
        let mut k = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant k <= 64, samples.len() == 64, fraction_bits == 0,
                0 < precision@ <= 38,
                level_shift == 1i64 << ((precision@ - 1) as u8),
                maximum == (1u64 << precision@) - 1,
                forall |j: int| 0 <= j < 64 ==> #[trigger] samples@[j] <= i64::MAX as int - level_shift as int,
                forall |j: int| 0 <= j < k ==>
                    crate::specs::part1_decoded_unsigned_value(samples@[j], 0, level_shift, maximum)
                        == Ok(#[trigger] chunk@[j]),
            decreases 64 - k,
        ))]
        while k < 64 {
            let shifted = samples[k] + level_shift;
            let clamped = if shifted < 0 {
                0_u64
            } else {
                (shifted as u64).min(maximum)
            };
            chunk[k] = clamped;
            k += 1;
        }
    } else if fraction_bits == 16 {
        let mut k = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant k <= 64, samples.len() == 64, fraction_bits == 16,
                0 < precision@ <= 38,
                level_shift == 1i64 << ((precision@ - 1) as u8),
                maximum == (1u64 << precision@) - 1,
                forall |j: int| 0 <= j < 64 ==> #[trigger] samples@[j] <= i64::MAX as int - 32768,
                forall |j: int| 0 <= j < k ==>
                    crate::specs::part1_decoded_unsigned_value(samples@[j], 16, level_shift, maximum)
                        == Ok(#[trigger] chunk@[j]),
            decreases 64 - k,
        ))]
        while k < 64 {
            let rounded = (samples[k] + 32_768) >> 16;
            #[cfg(verus_keep_ghost)]
            proof! {
                let s = samples[k as int] + 32_768;
                assert(-140737488355328i64 <= (s >> 16i64) <= 140737488355327i64) by (bit_vector);
                assert(0 < level_shift <= 137438953472i64) by (bit_vector)
                    requires 0 < precision@ <= 38, level_shift == 1i64 << ((precision@ - 1) as u8);
            }
            let shifted = rounded + level_shift;
            let clamped = if shifted < 0 {
                0_u64
            } else {
                (shifted as u64).min(maximum)
            };
            chunk[k] = clamped;
            k += 1;
        }
    } else {
        let bias = 1_i64 << u32::from(fraction_bits - 1);
        let shift = u32::from(fraction_bits);
        let mut k = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant k <= 64, samples.len() == 64, 0 < fraction_bits <= 62,
                0 < precision@ <= 38,
                bias == 1i64 << ((fraction_bits - 1) as u32),
                shift == fraction_bits as u32,
                level_shift == 1i64 << ((precision@ - 1) as u8),
                maximum == (1u64 << precision@) - 1,
                forall |j: int| 0 <= j < 64 ==> #[trigger] samples@[j] <= i64::MAX as int - bias as int,
                forall |j: int| 0 <= j < k ==>
                    crate::specs::part1_decoded_unsigned_value(samples@[j], fraction_bits, level_shift, maximum)
                        == Ok(#[trigger] chunk@[j]),
            decreases 64 - k,
        ))]
        while k < 64 {
            let rounded = (samples[k] + bias) >> shift;
            #[cfg(verus_keep_ghost)]
            proof! {
                let s = samples[k as int] + bias;
                assert(-4611686018427387904i64 <= (s >> shift) <= 4611686018427387903i64) by (bit_vector)
                    requires 1u32 <= shift <= 62u32;
                assert(0 < level_shift <= 137438953472i64) by (bit_vector)
                    requires 0 < precision@ <= 38, level_shift == 1i64 << ((precision@ - 1) as u8);
            }
            let shifted = rounded + level_shift;
            let clamped = if shifted < 0 {
                0_u64
            } else {
                (shifted as u64).min(maximum)
            };
            chunk[k] = clamped;
            k += 1;
        }
    }
    output.extend_from_slice(&chunk);
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires samples.len() == 64,
    ensures result == forall |k: int| 0 <= k < 64 ==> #[trigger] samples@[k] <= max_allowed,
))]
#[inline(always)]
fn chunk_le_max(samples: &[i64], max_allowed: i64) -> bool {
    let mut k = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant k <= 64, samples.len() == 64,
            forall |j: int| 0 <= j < k ==> #[trigger] samples@[j] <= max_allowed,
        decreases 64 - k,
    ))]
    while k < 64 {
        if samples[k] > max_allowed {
            return false;
        }
        k += 1;
    }
    true
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
        ensures crate::specs::part2_typed_samples_result(decoded_component_view(*self),crate::limits::resource_decoded_bytes_limit(limits),decoded_typed_samples_outcome(result)),
        decoded_typed_samples_outcome(result)!=Err(DecodeError::AllocationFailed) ==> decoded_typed_samples_outcome(result) == crate::specs::part1_decoded_component_typed_samples(
            decoded_component_view(*self), crate::limits::resource_decoded_bytes_limit(limits),
        ),
    ))]
    pub fn typed_samples(&self, limits: &ResourceLimits) -> Result<TypedSamples, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost source=decoded_component_view(*self);}
        #[cfg(verus_keep_ghost)]
        proof! {reveal(decoded_component_view);crate::specs::part2_typed_samples_normal(source,crate::limits::resource_decoded_bytes_limit(limits));}
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
            let reserved = if self.samples.is_empty() {
                Ok(Vec::new())
            } else {
                crate::allocation::empty_with_capacity(self.samples.len())
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                let context=crate::specs::Part2TypedCapacityContext::Samples {source,maximum:crate::limits::resource_decoded_bytes_limit(limits)};
                crate::specs::part2_typed_capacity_observed(context,crate::allocation::inspection_capacity_outcome(reserved));
                if reserved.is_err(){crate::specs::part2_typed_samples_refused(source,crate::limits::resource_decoded_bytes_limit(limits));}
            }
            let mut output = reserved?;
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
                    source==decoded_component_view(*self),
                    crate::specs::part2_typed_samples_result(source,crate::limits::resource_decoded_bytes_limit(limits),crate::specs::part1_decoded_component_typed_samples(source,crate::limits::resource_decoded_bytes_limit(limits))),
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
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(index)?;
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
            let reserved = if self.samples.is_empty() {
                Ok(Vec::new())
            } else {
                crate::allocation::empty_with_capacity(self.samples.len())
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                let context=crate::specs::Part2TypedCapacityContext::Samples {source,maximum:crate::limits::resource_decoded_bytes_limit(limits)};
                crate::specs::part2_typed_capacity_observed(context,crate::allocation::inspection_capacity_outcome(reserved));
                if reserved.is_err(){crate::specs::part2_typed_samples_refused(source,crate::limits::resource_decoded_bytes_limit(limits));}
            }
            let mut output = reserved?;
            let mut index = 0;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_decoded_unsigned_empty(
                    self.samples@, self.fraction_bits, self.info.precision,
                );
            }
            let fast_max = if self.fraction_bits == 0 {
                Some(i64::MAX - level_shift)
            } else if self.fraction_bits <= 62 {
                Some(i64::MAX - (1_i64 << u32::from(self.fraction_bits - 1)))
            } else {
                None
            };
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant index <= self.samples.len(),
                    source==decoded_component_view(*self),
                    crate::specs::part2_typed_samples_result(source,crate::limits::resource_decoded_bytes_limit(limits),crate::specs::part1_decoded_component_typed_samples(source,crate::limits::resource_decoded_bytes_limit(limits))),
                    0 < self.info.precision <= 38,
                    !self.info.signed,
                    level_shift == 1i64 << ((self.info.precision - 1) as u8),
                    unsigned_max == (1u64 << self.info.precision) - 1,
                    fast_max == if self.fraction_bits == 0 {
                        Some(i64::MAX - level_shift)
                    } else if self.fraction_bits <= 62 {
                        Some(i64::MAX - (1i64 << ((self.fraction_bits - 1) as u32)))
                    } else {
                        None
                    },
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
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(index)?;
                let fast_slice = if self.samples.len() - index >= 64 {
                    fast_max
                } else {
                    None
                };
                if let Some(max_allowed) = fast_slice {
                    let slice = &self.samples[index..index + 64];
                    if chunk_le_max(slice, max_allowed) {
                        #[cfg(verus_keep_ghost)]
                        proof_decl! { let ghost before_len = output.len(); let ghost before_out = output@; }
                        append_typed_unsigned_chunk(
                            slice,
                            &mut output,
                            self.fraction_bits,
                            level_shift,
                            unsigned_max,
                            #[cfg(verus_keep_ghost)]
                            Ghost(self.info.precision),
                        );
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            let mut k: nat = 0;
                            while k < 64
                                invariant
                                    k <= 64,
                                    index + 64 <= self.samples.len(),
                                    before_len == before_out.len(),
                                    output.len() == before_len + 64,
                                    output@.subrange(0, before_len as int) == before_out,
                                    crate::specs::part1_decoded_unsigned_prefix(
                                        self.samples@, self.fraction_bits, self.info.precision, index as nat + k,
                                    ) == Ok(output@.subrange(0, (before_len + k) as int)),
                                    forall |j: int| 0 <= j < 64 ==>
                                        crate::specs::part1_decoded_unsigned_value(self.samples@[index as int + j], self.fraction_bits, level_shift, unsigned_max)
                                            == Ok(#[trigger] output@[before_len as int + j]),
                                decreases 64 - k,
                            {
                                crate::proofs::production_impl::production_decoded_unsigned_step(
                                    self.samples@, self.fraction_bits, self.info.precision, index as nat + k,
                                );
                                assert(output@.subrange(0, (before_len + k) as int).push(output@[before_len as int + k as int])
                                    =~= output@.subrange(0, (before_len + k + 1) as int));
                                k = k + 1;
                            }
                            assert(output@.subrange(0, output.len() as int) =~= output@);
                        }
                        index += 64;
                        continue;
                    }
                }
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
