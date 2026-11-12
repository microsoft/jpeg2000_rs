//! Nonlinear point transforms and arbitrary wavelet-kernel markers.

use super::profile::maximum_u32_for_bits;
use super::reader::{read_u16, read_u32};
use super::{
    ArbitraryKernel, DecodeError, KernelCoefficient, KernelLiftingStep, MalformedKind,
    NonlinearPointTransform, Parser, Part2Extensions, Segment,
};
#[cfg(verus_keep_ghost)]
use super::{
    atk_payload_outcome, kernel_coefficient_outcome, kernel_step_outcome, nlt_payload_outcome,
    owned_extensions_view, owned_kernel_view, owned_nonlinear_list_view, owned_nonlinear_view,
    parser_view, raw_kernel_coefficient_option, raw_kernel_coefficient_view,
    raw_kernel_coefficients_view, raw_kernel_step_view, raw_kernel_steps_view, raw_kernel_view,
    segment_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), owned_extensions_view(final(extensions)))
            == crate::specs::part1_parse_nlt(parser_view(old(self)), segment_view(segment),
                components, owned_extensions_view(old(extensions))),
    ))]
    pub(super) fn parse_nlt(
        &mut self,
        segment: Segment<'a>,
        components: u16,
        extensions: &mut Part2Extensions,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = parser_view(self);
            let ghost extension_input = owned_extensions_view(extensions);
            let ghost goal = crate::specs::part1_parse_nlt(input, segment_view(segment), components, extension_input);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_nlt); }
        self.charge_extension_metadata(segment, extensions)?;
        let replacement = self.decode_nlt_payload(segment, components)?;
        let local_count = extensions
            .nonlinear_local_count
            .unwrap_or(extensions.nonlinear_transforms.len());
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost charged_parser = parser_view(self);
            let ghost charged_extensions = owned_extensions_view(extensions);
            let ghost decoded = owned_nonlinear_view(&replacement);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(owned_nonlinear_view);
            reveal(owned_nonlinear_list_view);
            assert(goal == (crate::specs::part1_nlt_replace(charged_extensions, decoded, 0, local_count, segment.offset).0,
                charged_parser, crate::specs::part1_nlt_replace(charged_extensions, decoded, 0, local_count, segment.offset).1));
            reveal_with_fuel(crate::specs::part1_nlt_replace, 1);
        }
        if local_count > extensions.nonlinear_transforms.len() {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= local_count, local_count <= extensions.nonlinear_transforms.len(),
                input == parser_view(old(self)),
                extension_input == owned_extensions_view(old(extensions)),
                parser_view(self) == charged_parser,
                owned_extensions_view(extensions) == charged_extensions,
                owned_nonlinear_view(&replacement) == decoded,
                goal == crate::specs::part1_parse_nlt(input, segment_view(segment), components, extension_input),
                goal == (crate::specs::part1_nlt_replace(charged_extensions, decoded, position as nat, local_count, segment.offset).0,
                    charged_parser, crate::specs::part1_nlt_replace(charged_extensions, decoded, position as nat, local_count, segment.offset).1),
            decreases local_count - position,
        ))]
        while position < local_count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_nlt_replace, 1); reveal(owned_nonlinear_view); }
            if extensions.nonlinear_transforms[position].component == replacement.component {
                extensions.nonlinear_transforms[position] = replacement;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(owned_extensions_view(extensions).nonlinear =~=
                        charged_extensions.nonlinear.update(position as int, decoded));
                }
                return Ok(());
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_nlt_replace, 1); }
        let next_count = match extensions.nonlinear_local_count {
            Some(count) => Some(match count.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            }),
            None => None,
        };
        extensions
            .nonlinear_transforms
            .insert(local_count, replacement);
        extensions.nonlinear_local_count = next_count;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(owned_extensions_view(extensions).nonlinear =~= charged_extensions.nonlinear.insert(local_count as int, decoded));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures nlt_payload_outcome(result) == crate::specs::part1_nlt_payload(segment_view(segment), components),
    ))]
    pub(super) fn decode_nlt_payload(
        &self,
        segment: Segment<'a>,
        components: u16,
    ) -> Result<NonlinearPointTransform, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_nlt_payload); reveal(crate::specs::part1_nlt_header);
            reveal(crate::specs::part1_nlt_points); reveal(crate::specs::part1_nlt_points_header);
            reveal(crate::specs::part1_copy_segment_tail); reveal(owned_nonlinear_view);
        }
        if segment.payload.len() < 4 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let raw_component = read_u16([segment.payload[0], segment.payload[1]]);
        let component = if raw_component == u16::MAX {
            None
        } else if raw_component < components {
            Some(raw_component)
        } else {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        };
        let precision = crate::refinement::cbd_precision(segment.payload[2]);
        let transform_type = segment.payload[3];
        if precision > 38 || transform_type > 4 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        if matches!(transform_type, 0 | 3) && segment.payload.len() != 4 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let mut d_min = None;
        let mut d_max = None;
        let mut point_bits = None;
        let mut points = Vec::new();
        let mut gamma_parameters = None;
        if transform_type == 1 {
            gamma_parameters = Some(self.decode_nlt_gamma(segment)?);
        }
        if matches!(transform_type, 2 | 4) {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_segment_byte); }
            if segment.payload.len() < 15 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
            }
            let stored_points = read_u16([
                self.segment_byte(segment, 4, 0)?,
                self.segment_byte(segment, 4, 1)?,
            ]);
            if stored_points == 0 || stored_points > 8191 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
            let count = match stored_points.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            let minimum = read_u32([
                self.segment_byte(segment, 6, 0)?,
                self.segment_byte(segment, 6, 1)?,
                self.segment_byte(segment, 6, 2)?,
                self.segment_byte(segment, 6, 3)?,
            ]);
            let maximum = read_u32([
                self.segment_byte(segment, 10, 0)?,
                self.segment_byte(segment, 10, 1)?,
                self.segment_byte(segment, 10, 2)?,
                self.segment_byte(segment, 10, 3)?,
            ]);
            let bits = segment.payload[14];
            if minimum >= maximum || bits == 0 || bits > 32 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
            let width = if bits <= 8 {
                1_usize
            } else if bits <= 16 {
                2_usize
            } else {
                4_usize
            };
            let point_bytes = match usize::from(count).checked_mul(width) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            let expected = match 15_usize.checked_add(point_bytes) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            if segment.payload.len() != expected {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost header = (count, minimum, maximum, bits, width);
                let ghost values = Seq::new(count as nat, |index: int|
                    crate::specs::part1_nlt_point_value(segment.payload@, width, index));
            }
            let mut point = 0_u16;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant point <= count, 1 < count <= 8192,
                        0 < bits <= 32,
                        width == crate::specs::part1_nlt_point_width(bits),
                        segment.payload.len() == 15 + count as int * width as int,
                        crate::specs::part1_nlt_points_header(segment_view(segment)) == Ok(header),
                        crate::specs::part1_nlt_header(segment_view(segment), components) ==
                            Ok((component, precision, crate::specs::part2_cbd_signed(segment.payload@[2]), transform_type)),
                        transform_type == 2 || transform_type == 4,
                        header == (count, minimum, maximum, bits, width),
                        values == Seq::new(count as nat, |index: int|
                            crate::specs::part1_nlt_point_value(segment.payload@, width, index)),
                        points@ == values.subrange(0, point as int),
                        forall|index: int| 0 <= index < point ==>
                            values[index] <= crate::specs::part1_nlt_point_maximum(bits),
                    decreases count - point,
                )
            )]
            while point < count {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part1_segment_byte);
                    reveal(crate::specs::part1_nlt_payload); reveal(crate::specs::part1_nlt_header);
                    reveal(crate::specs::part1_nlt_points);
                }
                let relative = match usize::from(point).checked_mul(width) {
                    Some(value) => value,
                    None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
                };
                let position = match 15_usize.checked_add(relative) {
                    Some(value) => value,
                    None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
                };
                let value = if width == 1 {
                    u32::from(self.segment_byte(segment, position, 0)?)
                } else if width == 2 {
                    u32::from(read_u16([
                        self.segment_byte(segment, position, 0)?,
                        self.segment_byte(segment, position, 1)?,
                    ]))
                } else {
                    read_u32([
                        self.segment_byte(segment, position, 0)?,
                        self.segment_byte(segment, position, 1)?,
                        self.segment_byte(segment, position, 2)?,
                        self.segment_byte(segment, position, 3)?,
                    ])
                };
                #[cfg(verus_keep_ghost)]
                proof! { assert(value == values[point as int]); }
                let maximum_point = if bits == 32 {
                    u32::MAX
                } else {
                    maximum_u32_for_bits(bits)?
                };
                if value > maximum_point {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(values[point as int] > crate::specs::part1_nlt_point_maximum(bits));
                        assert(crate::specs::part1_nlt_points(segment_view(segment)) ==
                            Err(crate::specs::part1_codestream_malformed(segment.offset, MalformedKind::InvalidTransform)));
                    }
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
                points.push(value);
                #[cfg(verus_keep_ghost)]
                proof! { assert(values.subrange(0, point as int + 1) =~= values.subrange(0, point as int).push(value)); }
                point = match point.checked_add(1) {
                    Some(value) => value,
                    None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
                };
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(values.subrange(0, point as int) =~= values);
                assert(crate::specs::part1_nlt_points(segment_view(segment)) == Ok((minimum, maximum, bits, points@)));
            }
            d_min = Some(minimum);
            d_max = Some(maximum);
            point_bits = Some(bits);
        }
        Ok(NonlinearPointTransform {
            component,
            precision,
            signed: crate::refinement::cbd_signed(segment.payload[2]),
            transform_type,
            parameters: self.copy_segment_tail(segment, 4)?,
            d_min,
            d_max,
            point_bits,
            points,
            gamma_parameters,
        })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), owned_extensions_view(final(extensions)))
            == crate::specs::part1_parse_atk(parser_view(old(self)), segment_view(segment), owned_extensions_view(old(extensions))),
    ))]
    pub(super) fn parse_atk(
        &mut self,
        segment: Segment<'a>,
        extensions: &mut Part2Extensions,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = parser_view(self);
            let ghost extension_input = owned_extensions_view(extensions);
            let ghost goal = crate::specs::part1_parse_atk(input, segment_view(segment), extension_input);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_parse_atk); }
        self.charge_extension_metadata(segment, extensions)?;
        let replacement = self.decode_atk_payload(segment)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost charged_parser = parser_view(self);
            let ghost charged_extensions = owned_extensions_view(extensions);
            let ghost decoded = owned_kernel_view(&replacement);
            let ghost target = crate::specs::part1_atk_replace(charged_extensions.kernels, decoded, 0);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(owned_kernel_view);
            assert(goal == (Ok(()), charged_parser, crate::specs::part1_extension_kernels(charged_extensions, target)));
        }
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= extensions.arbitrary_kernels.len(),
                input == parser_view(old(self)), extension_input == owned_extensions_view(old(extensions)),
                parser_view(self) == charged_parser, owned_extensions_view(extensions) == charged_extensions,
                owned_kernel_view(&replacement) == decoded,
                target == crate::specs::part1_atk_replace(charged_extensions.kernels, decoded, position as nat),
                goal == crate::specs::part1_parse_atk(input, segment_view(segment), extension_input),
                goal == (Ok(()), charged_parser, crate::specs::part1_extension_kernels(charged_extensions, target)),
            decreases extensions.arbitrary_kernels.len() - position,
        ))]
        while position < extensions.arbitrary_kernels.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_atk_replace, 1); reveal(owned_kernel_view); }
            if extensions.arbitrary_kernels[position].index == replacement.index {
                extensions.arbitrary_kernels[position] = replacement;
                #[cfg(verus_keep_ghost)]
                proof! { assert(owned_extensions_view(extensions).kernels =~= charged_extensions.kernels.update(position as int, decoded)); }
                return Ok(());
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_atk_replace, 1); }
        extensions.arbitrary_kernels.push(replacement);
        #[cfg(verus_keep_ghost)]
        proof! { assert(owned_extensions_view(extensions).kernels =~= charged_extensions.kernels.push(decoded)); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures atk_payload_outcome(result) == crate::specs::part1_atk_payload(self.position, segment_view(segment)),
    ))]
    pub(super) fn decode_atk_payload(
        &self,
        segment: Segment<'a>,
    ) -> Result<ArbitraryKernel, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost goal = crate::specs::part1_atk_payload(self.position, segment_view(segment)); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_atk_payload); reveal(crate::specs::part1_atk_header); }
        if segment.payload.len() < 7 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let descriptor = read_u16([segment.payload[0], segment.payload[1]]);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(descriptor & 0xff <= 255u16) by (bit_vector);
            assert((descriptor >> 8) & 7 <= 7u16) by (bit_vector);
        }
        let index = (descriptor & 0xff) as u8;
        let coefficient_type = ((descriptor >> 8) & 7) as u8;
        if index < 2 || coefficient_type > 4 || descriptor & 0x8000 != 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let width = match coefficient_type {
            0 => 1_usize,
            1 => 2,
            2 => 4,
            3 => 8,
            4 => 16,
            _ => {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
        };
        let whole_sample_filter = descriptor & 0x0800 != 0;
        let reversible = descriptor & 0x1000 != 0;
        let initial_odd = descriptor & 0x2000 != 0;
        let whole_sample_extension = descriptor & 0x4000 != 0;
        let mut position = 2_usize;
        let scaling = if reversible {
            None
        } else {
            let coefficient =
                self.read_kernel_coefficient(segment, position, width, coefficient_type)?;
            position = match position.checked_add(width) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            Some(coefficient)
        };
        let step_count = usize::from(self.segment_byte(segment, position, 0)?);
        position = match position.checked_add(1) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost header = crate::specs::Part1AtkHeader {
                index, descriptor, coefficient_type, width, reversible, whole_sample_filter, initial_odd, whole_sample_extension,
                scaling: raw_kernel_coefficient_option(scaling), step_count, position,
            };
            let ghost target = crate::specs::part1_atk_steps(self.position, segment_view(segment), position,
                width, coefficient_type, reversible, whole_sample_filter, step_count as nat, Seq::empty());
        }
        let mut steps = Vec::with_capacity(step_count);
        #[cfg(verus_keep_ghost)]
        proof! { assert(raw_kernel_steps_view(steps@) =~= Seq::empty()); }
        let mut step = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant step <= step_count <= 255,
                    header.index == index, header.descriptor == descriptor, header.coefficient_type == coefficient_type,
                    header.width == width, header.reversible == reversible, header.whole_sample_filter == whole_sample_filter,
                    header.initial_odd == initial_odd, header.whole_sample_extension == whole_sample_extension,
                    header.scaling == raw_kernel_coefficient_option(scaling),
                    target == crate::specs::part1_atk_steps(self.position, segment_view(segment), position,
                        width, coefficient_type, reversible, whole_sample_filter, (step_count - step) as nat, raw_kernel_steps_view(steps@)),
                    goal == crate::specs::part1_atk_payload(self.position, segment_view(segment)),
                    goal == match target {
                        Err(error) => Err(error),
                        Ok((values, next)) => if next != segment.payload.len() {
                            Err(crate::specs::part1_codestream_malformed(segment.offset, MalformedKind::InvalidMarkerLength))
                        } else { Ok(crate::specs::part1_atk_kernel(header, values)) },
                    },
                decreases step_count - step,
            )
        )]
        while step < step_count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_atk_steps, 1); }
            let (decoded, next) = self.decode_atk_step(
                segment,
                position,
                width,
                coefficient_type,
                reversible,
                whole_sample_filter,
            )?;
            position = next;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous = raw_kernel_steps_view(steps@); let ghost value = raw_kernel_step_view(decoded); }
            steps.push(decoded);
            #[cfg(verus_keep_ghost)]
            proof! { assert(raw_kernel_steps_view(steps@) =~= previous.push(value)); }
            step = match step.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_atk_steps, 1);
            reveal(owned_kernel_view); reveal(raw_kernel_view);
        }
        if position != segment.payload.len() {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        Ok(ArbitraryKernel {
            index,
            reversible,
            descriptor,
            coefficient_type,
            whole_sample_filter,
            initial_odd,
            whole_sample_extension,
            scaling,
            steps,
        })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures kernel_step_outcome(result) == crate::specs::part1_atk_step(
            self.position, segment_view(segment), start, width, coefficient_type, reversible, whole_sample_filter),
    ))]
    pub(super) fn decode_atk_step(
        &self,
        segment: Segment<'a>,
        start: usize,
        width: usize,
        coefficient_type: u8,
        reversible: bool,
        whole_sample_filter: bool,
    ) -> Result<(KernelLiftingStep, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost goal = crate::specs::part1_atk_step(
                self.position, segment_view(segment), start, width, coefficient_type, reversible, whole_sample_filter);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_atk_step); reveal(crate::specs::part1_atk_step_header); }
        let mut position = start;
        let offset = if whole_sample_filter {
            0
        } else {
            self.segment_byte(segment, position, 0)? as i8
        };
        if !whole_sample_filter {
            position = match position.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
        }
        let exponent = if reversible {
            let value = self.segment_byte(segment, position, 0)?;
            position = match position.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            value
        } else {
            0
        };
        let residue = if reversible {
            let value = self.read_kernel_coefficient(segment, position, width, coefficient_type)?;
            position = match position.checked_add(width) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            Some(value)
        } else {
            None
        };
        let coefficient_count = usize::from(self.segment_byte(segment, position, 0)?);
        position = match position.checked_add(1) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        if coefficient_count == 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost target = crate::specs::part1_atk_coefficients(
                self.position, segment_view(segment), position, width, coefficient_type, coefficient_count as nat, Seq::empty());
        }
        let mut coefficients = Vec::with_capacity(coefficient_count);
        #[cfg(verus_keep_ghost)]
        proof! { assert(raw_kernel_coefficients_view(coefficients@) =~= Seq::empty()); }
        let mut coefficient = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant coefficient <= coefficient_count <= 255,
                target == crate::specs::part1_atk_coefficients(self.position, segment_view(segment), position,
                    width, coefficient_type, (coefficient_count - coefficient) as nat,
                    raw_kernel_coefficients_view(coefficients@)),
                goal == crate::specs::part1_atk_step(self.position, segment_view(segment), start,
                    width, coefficient_type, reversible, whole_sample_filter),
                goal == match target {
                    Err(error) => Err(error),
                    Ok((values, next)) => Ok(((offset, exponent, raw_kernel_coefficient_option(residue), values), next)),
                },
            decreases coefficient_count - coefficient,
        ))]
        while coefficient < coefficient_count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_atk_coefficients, 1); }
            let value = self.read_kernel_coefficient(segment, position, width, coefficient_type)?;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous = raw_kernel_coefficients_view(coefficients@); }
            coefficients.push(value);
            #[cfg(verus_keep_ghost)]
            proof! { assert(raw_kernel_coefficients_view(coefficients@) =~= previous.push(raw_kernel_coefficient_view(value))); }
            position = match position.checked_add(width) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            coefficient = match coefficient.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_atk_coefficients, 1); reveal(raw_kernel_step_view); }
        Ok((
            KernelLiftingStep {
                offset,
                exponent,
                residue,
                coefficients,
            },
            position,
        ))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures kernel_coefficient_outcome(result) == crate::specs::part1_kernel_coefficient(
            self.position, segment_view(segment), position, width, coefficient_type),
    ))]
    pub(super) fn read_kernel_coefficient(
        &self,
        segment: Segment<'a>,
        position: usize,
        width: usize,
        coefficient_type: u8,
    ) -> Result<KernelCoefficient, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_kernel_coefficient); reveal(raw_kernel_coefficient_view); }
        if width == 0 || width > 16 {
            return Err(self.malformed_here(MalformedKind::InvalidTransform));
        }
        let end = match position.checked_add(width) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        let source = match segment.payload.get(position..end) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
            }
        };
        let mut bytes = [0_u8; 16];
        let start = match bytes.len().checked_sub(width) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        let mut copied = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant 0 < width <= 16, start == 16 - width, copied <= width,
                source.len() == width,
                source@ == segment.payload@.subrange(position as int, end as int),
                forall|index: int| 0 <= index < 16 ==> bytes@[index] ==
                    if start <= index < start + copied { source@[index - start as int] } else { 0u8 },
            decreases width - copied,
        ))]
        while copied < width {
            bytes[start + copied] = source[copied];
            copied += 1;
        }
        let negative_integer = match source.first() {
            Some(byte) => *byte & 0x80 != 0,
            None => false,
        };
        if coefficient_type <= 1 && negative_integer {
            let mut fill = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant fill <= start, start == 16 - width, 0 < width <= 16,
                        source.len() == width,
                        source@ == segment.payload@.subrange(position as int, end as int),
                        coefficient_type <= 1, source@[0] & 0x80 != 0,
                        forall|index: int| 0 <= index < 16 ==> bytes@[index] ==
                            if index < fill { 255u8 } else if index < start { 0u8 } else { source@[index - start as int] },
                    decreases start - fill,
                )
            )]
            while fill < start {
                bytes[fill] = 0xff;
                fill += 1;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(bytes@ =~= crate::specs::part1_kernel_coefficient_bytes(
                segment.payload@, position, width, coefficient_type));
        }
        Ok(KernelCoefficient {
            bytes,
            width: width as u8,
        })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_nlt_gamma(segment_view(segment)),
    ))]
    pub(super) fn decode_nlt_gamma(&self, segment: Segment<'a>) -> Result<[u32; 5], DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_nlt_gamma); }
        if segment.payload.len() != 19 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let mut parameters = [0_u32; 5];
        let mut parameter = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant parameter <= 5, segment.payload.len() == 19,
                forall|index: int| 0 <= index < parameter ==>
                    parameters@[index] == crate::specs::part1_nlt_gamma_word(segment.payload@, index),
            decreases 5 - parameter,
        ))]
        while parameter < parameters.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_segment_byte); }
            let relative = match parameter.checked_mul(3) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            let position = match 4_usize.checked_add(relative) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
            parameters[parameter] = (u32::from(self.segment_byte(segment, position, 0)?) << 16)
                | (u32::from(self.segment_byte(segment, position, 1)?) << 8)
                | u32::from(self.segment_byte(segment, position, 2)?);
            parameter = match parameter.checked_add(1) {
                Some(value) => value,
                None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let expected = [
                crate::specs::part1_nlt_gamma_word(segment.payload@, 0),
                crate::specs::part1_nlt_gamma_word(segment.payload@, 1),
                crate::specs::part1_nlt_gamma_word(segment.payload@, 2),
                crate::specs::part1_nlt_gamma_word(segment.payload@, 3),
                crate::specs::part1_nlt_gamma_word(segment.payload@, 4),
            ];
            assert(parameters@ =~= expected@);
            assert(parameters =~= expected);
        }
        if parameters[0] == 0 || parameters[1] == 0 || parameters[3] == 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        Ok(parameters)
    }
}
