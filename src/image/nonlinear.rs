use super::arithmetic::{
    arithmetic_overflow, index, invalid_image, invalid_transform, validate_bytes,
};
use super::mct::charge_mct_work;
use super::nonlinear_math::inverse_nlt_sample;
use super::{NonlinearRegion, TypedComponent, TypedImage, TypedSamples};
#[cfg(verus_keep_ghost)]
use super::{
    nlt_scratch_view, typed_component_definitions, typed_component_view,
    typed_image_component_views, typed_image_definition_views, typed_image_geometry,
    typed_image_value_view,
};
#[cfg(test)]
use crate::Resource;
#[cfg(test)]
use crate::codestream::Part2Extensions;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl TypedImage {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_nlt_image_storage_result(crate::specs::Part2NltImageStorageContext {
            source:typed_image_value_view(*old(self)),regions:crate::decode::nonlinear_regions_view(regions@),
            maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
            maximum_work:crate::limits::resource_work_limit(limits),
        },(result,typed_image_value_view(*final(self)))),
        result != Err(DecodeError::AllocationFailed) ==>
            (result, typed_image_value_view(*final(self))) == crate::specs::part2_apply_nonlinear_regions(
            typed_image_value_view(*old(self)), crate::decode::nonlinear_regions_view(regions@),
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
        ),
    ))]
    pub(crate) fn apply_nonlinear_regions(
        &mut self,
        regions: &[NonlinearRegion<'_>],
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = typed_image_value_view(*self);
            let ghost region_views = crate::decode::nonlinear_regions_view(regions@);
            let ghost byte_limit = crate::limits::resource_decoded_bytes_limit(limits);
            let ghost work_limit = crate::limits::resource_work_limit(limits);
            let ghost expected = crate::specs::part2_nlt_apply_components(initial, 0, region_views, byte_limit, work_limit, 0);
            let ghost storage_context=crate::specs::Part2NltImageStorageContext {
                source:initial,regions:region_views,maximum_bytes:byte_limit,maximum_work:work_limit};
            let ghost mut storage_prefix=Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_apply_nonlinear_regions);
            crate::specs::part2_nlt_image_storage_normal(storage_context);
            assert forall|tail:Seq<crate::specs::Part2JpipSnapshotEvent>|
                crate::specs::part2_nlt_image_storage_run(storage_context,storage_prefix+tail)
                    ==crate::specs::part2_nlt_image_components_storage_run(storage_context,initial,0,0,tail) by {
                assert(storage_prefix+tail =~= tail);
            }
        }
        let mut work = 0_u64;
        let mut component_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component_index <= self.components.len(),
                initial == typed_image_value_view(*old(self)),
                initial.0 == typed_image_geometry(self),
                initial.2 == typed_image_definition_views(self),
                region_views == crate::decode::nonlinear_regions_view(regions@),
                byte_limit == crate::limits::resource_decoded_bytes_limit(limits),
                work_limit == crate::limits::resource_work_limit(limits),
                (expected.1, expected.0) == crate::specs::part2_apply_nonlinear_regions(initial, region_views, byte_limit, work_limit),
                expected == crate::specs::part2_nlt_apply_components(
                    typed_image_value_view(*self), component_index as nat, region_views, byte_limit, work_limit, work,
                ),
                storage_context==(crate::specs::Part2NltImageStorageContext {
                    source:initial,regions:region_views,maximum_bytes:byte_limit,maximum_work:work_limit}),
                crate::specs::part2_cold_phase(|events|crate::specs::part2_nlt_image_storage_run(storage_context,events),
                    storage_prefix,|events|crate::specs::part2_nlt_image_components_storage_run(storage_context,
                        typed_image_value_view(*self),component_index as nat,work,events)),
                decreases self.components.len() - component_index,
            )
        )]
        while component_index < self.components.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part2_nlt_apply_components, 1); }
            if component_index > usize::from(u16::MAX) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_nlt_image_storage_boundary(storage_context,storage_prefix,
                        typed_image_value_view(*self),component_index as nat,work);
                }
                return Err(arithmetic_overflow());
            }
            let component_number = component_index as u16;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost before = typed_image_value_view(*self);
                let ghost native_before = self.components@;
                let ghost source_view = before.1[component_index as int];
                let ghost component_expected = crate::specs::part2_nlt_component(
                    source_view, component_number, region_views, byte_limit, work_limit, work,
                );
            }
            let outcome = {
                let component = self
                    .components
                    .get_mut(component_index)
                    .ok_or_else(invalid_image)?;
                component.apply_nonlinear_regions(component_number, regions, work, limits)
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_nlt_component_mutation);
                let ghost updated=typed_component_view(&self.components@[component_index as int]);
                let ghost child=crate::specs::part2_nlt_image_component_context(storage_context,before,component_index as nat,work);
                crate::specs::part2_nlt_component_storage_frames(child,(outcome,updated));
                assert(typed_image_component_views(self) =~= before.1.update(component_index as int, updated));
                assert(typed_image_definition_views(self) =~= before.2);
                if let Err(error)=outcome {
                    assert(updated==source_view);
                    assert(typed_image_value_view(*self)==before);
                    crate::specs::part2_nlt_image_storage_component_error(storage_context,storage_prefix,before,
                        component_index as nat,work,error);
                }else if let Ok(next_work)=outcome {
                    storage_prefix=crate::specs::part2_nlt_image_storage_advance(storage_context,storage_prefix,before,
                        component_index as nat,work,updated,next_work);
                }
            }
            work = outcome?;
            component_index = component_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_nlt_apply_components, 1);
            crate::specs::part2_nlt_image_storage_boundary(storage_context,storage_prefix,
                typed_image_value_view(*self),component_index as nat,work);
        }
        Ok(())
    }
}

impl TypedComponent {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_nlt_component_storage_result(crate::specs::Part2NltComponentStorageContext {
            source:typed_component_view(old(self)),number:component_number,regions:crate::decode::nonlinear_regions_view(regions@),
            maximum_bytes:crate::limits::resource_decoded_bytes_limit(limits),
            maximum_work:crate::limits::resource_work_limit(limits),initial_work,
        },(result,typed_component_view(final(self)))),
        result != Err(DecodeError::AllocationFailed) ==>
            (result, typed_component_view(final(self))) == crate::specs::part2_nlt_component_mutation(
            typed_component_view(old(self)), component_number, crate::decode::nonlinear_regions_view(regions@),
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits), initial_work,
        ),
        typed_component_definitions(final(self)) == typed_component_definitions(old(self)),
    ))]
    pub(super) fn apply_nonlinear_regions(
        &mut self,
        component_number: u16,
        regions: &[NonlinearRegion<'_>],
        initial_work: u64,
        limits: &ResourceLimits,
    ) -> Result<u64, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source_view = typed_component_view(self);
            let ghost initial_defs = typed_component_definitions(self);
            let ghost region_views = crate::decode::nonlinear_regions_view(regions@);
            let ghost byte_limit = crate::limits::resource_decoded_bytes_limit(limits);
            let ghost work_limit = crate::limits::resource_work_limit(limits);
            let ghost storage_context=crate::specs::Part2NltComponentStorageContext {
                source:source_view,number:component_number,regions:region_views,
                maximum_bytes:byte_limit,maximum_work:work_limit,initial_work};
            let ghost component_expected = crate::specs::part2_nlt_component(
                source_view, component_number, region_views, byte_limit, work_limit, initial_work,
            );
            let ghost region_goal = crate::specs::part2_nlt_component_regions(
                source_view, component_number, region_views, 0, work_limit,
                nlt_scratch_view(Seq::new(crate::specs::part2_nlt_sample_count(source_view.samples), |i: int| None), None, initial_work),
            );
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_nlt_component_storage_normal(storage_context);
            reveal(crate::specs::part2_nlt_component_mutation);
        }
        let mut work = initial_work;
        let source_info = self.info;
        let sample_count = match &self.samples {
            TypedSamples::Signed(samples) => samples.len(),
            TypedSamples::Unsigned(samples) => samples.len(),
        };
        let scratch = nlt_scratch_values(sample_count);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_nlt_capacity_observed(storage_context,crate::specs::Part2NltCapacityRole::Scratch,
                crate::allocation::inspection_capacity_outcome(scratch));
            if let Err(error)=scratch {crate::specs::part2_nlt_component_scratch_refused(storage_context,error);}
        }
        let mut output = scratch?;
        let mut target = None;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(typed_component_view(self) == source_view);
            assert(output@ =~= Seq::new(crate::specs::part2_nlt_sample_count(source_view.samples), |i: int| None));
        }
        let mut region_index = 0_usize;
        #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant region_index <= regions.len(),
                    source_view == typed_component_view(old(self)),
                    initial_defs == typed_component_definitions(old(self)),
                    typed_component_view(self) == source_view,
                    self.channel_definitions@ == initial_defs,
                    source_info == source_view.info,
                    sample_count == crate::specs::part2_nlt_sample_count(source_view.samples),
                    output.len() == sample_count,
                    region_views == crate::decode::nonlinear_regions_view(regions@),
                    byte_limit == crate::limits::resource_decoded_bytes_limit(limits),
                    work_limit == crate::limits::resource_work_limit(limits),
                    component_expected == crate::specs::part2_nlt_component(
                        source_view, component_number, region_views, byte_limit, work_limit, initial_work,
                    ),
                    storage_context==(crate::specs::Part2NltComponentStorageContext {
                        source:source_view,number:component_number,regions:region_views,
                        maximum_bytes:byte_limit,maximum_work:work_limit,initial_work}),
                    crate::specs::part2_nlt_capacity_result(storage_context,crate::specs::Part2NltCapacityRole::Scratch,Ok(())),
                    crate::specs::part2_nlt_component_storage_result(storage_context,crate::specs::part2_nlt_component_mutation(
                        source_view,component_number,region_views,byte_limit,work_limit,initial_work)),
                    component_expected == match region_goal {
                        Err(error) => Err(error),
                        Ok(state) => crate::specs::part2_nlt_finish_component(source_view, state, byte_limit),
                    },
                    region_goal == crate::specs::part2_nlt_component_regions(
                        source_view, component_number, region_views, region_index as nat, work_limit,
                        nlt_scratch_view(output@, target, work),
                    ),
                    decreases regions.len() - region_index,
                )
            )]
        while region_index < regions.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_nlt_component_mutation);
                reveal_with_fuel(crate::specs::part2_nlt_component_regions, 1);
            }
            let region = regions.get(region_index).ok_or_else(invalid_image)?;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost region_view = crate::decode::nonlinear_region_view(region); }
            if region.component == component_number {
                if region.x0 >= region.x1
                    || region.y0 >= region.y1
                    || region.x1 > self.width
                    || region.y1 > self.height
                {
                    return Err(invalid_image());
                }
                let descriptor = (region.transform.precision(), region.transform.signed());
                if matches!(target, Some(existing) if existing != descriptor) {
                    return Err(invalid_transform());
                }
                target = Some(descriptor);
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost rows_goal = crate::specs::part2_nlt_region_rows(
                        source_view, region_view, region.y0, work_limit, nlt_scratch_view(output@, target, work),
                    );
                }
                let mut y = region.y0;
                #[cfg_attr(
                        verus_keep_ghost,
                        verus_spec(
                            invariant y <= region.y1,
                            y >= region.y0,
                            region_view == crate::decode::nonlinear_region_view(region),
                            region_view == region_views[region_index as int],
                            region_index < regions.len(),
                            source_view == typed_component_view(old(self)),
                            initial_defs == typed_component_definitions(old(self)),
                            typed_component_view(self) == source_view,
                            self.channel_definitions@ == initial_defs,
                            source_info == source_view.info,
                            sample_count == crate::specs::part2_nlt_sample_count(source_view.samples),
                            output.len() == sample_count,
                            target == Some((region_view.transform.precision, region_view.transform.signed)),
                            region_view.x0 < region_view.x1, region_view.y0 < region_view.y1,
                            region_view.x1 <= source_view.width, region_view.y1 <= source_view.height,
                            region_views == crate::decode::nonlinear_regions_view(regions@),
                            byte_limit == crate::limits::resource_decoded_bytes_limit(limits),
                            work_limit == crate::limits::resource_work_limit(limits),
                            component_expected == crate::specs::part2_nlt_component(
                                source_view, component_number, region_views, byte_limit, work_limit, initial_work,
                            ),
                            storage_context==(crate::specs::Part2NltComponentStorageContext {
                                source:source_view,number:component_number,regions:region_views,
                                maximum_bytes:byte_limit,maximum_work:work_limit,initial_work}),
                            crate::specs::part2_nlt_capacity_result(storage_context,crate::specs::Part2NltCapacityRole::Scratch,Ok(())),
                            crate::specs::part2_nlt_component_storage_result(storage_context,crate::specs::part2_nlt_component_mutation(
                                source_view,component_number,region_views,byte_limit,work_limit,initial_work)),
                            component_expected == match region_goal {
                                Err(error) => Err(error),
                                Ok(state) => crate::specs::part2_nlt_finish_component(source_view, state, byte_limit),
                            },
                            region_goal == match rows_goal {
                                Err(error) => Err(error),
                                Ok(state) => crate::specs::part2_nlt_component_regions(
                                    source_view, component_number, region_views, region_index as nat + 1, work_limit, state,
                                ),
                            },
                            rows_goal == crate::specs::part2_nlt_region_rows(
                                source_view, region_view, y, work_limit, nlt_scratch_view(output@, target, work),
                            ),
                            decreases region.y1 - y,
                        )
                    )]
                while y < region.y1 {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part2_nlt_component_mutation);
                        reveal_with_fuel(crate::specs::part2_nlt_region_rows, 1);
                    }
                    let mut x = region.x0;
                    if x > region.x1 {
                        return Err(invalid_image());
                    }
                    #[cfg(verus_keep_ghost)]
                    proof_decl! {
                        let ghost row_goal = crate::specs::part2_nlt_region_row(
                            source_view, region_view, y, region.x0, work_limit, nlt_scratch_view(output@, target, work),
                        );
                    }
                    #[cfg_attr(
                            verus_keep_ghost,
                            verus_spec(
                                invariant x <= region.x1,
                                x >= region.x0,
                                region.y0 <= y < region.y1,
                                region_view == crate::decode::nonlinear_region_view(region),
                                region_view == region_views[region_index as int],
                                region_index < regions.len(),
                                source_view == typed_component_view(old(self)),
                                initial_defs == typed_component_definitions(old(self)),
                                typed_component_view(self) == source_view,
                                self.channel_definitions@ == initial_defs,
                                source_info == source_view.info,
                                sample_count == crate::specs::part2_nlt_sample_count(source_view.samples),
                                output.len() == sample_count,
                                target == Some((region_view.transform.precision, region_view.transform.signed)),
                                region_view.x0 < region_view.x1, region_view.y0 < region_view.y1,
                                region_view.x1 <= source_view.width, region_view.y1 <= source_view.height,
                                region_views == crate::decode::nonlinear_regions_view(regions@),
                                byte_limit == crate::limits::resource_decoded_bytes_limit(limits),
                                work_limit == crate::limits::resource_work_limit(limits),
                                component_expected == crate::specs::part2_nlt_component(
                                    source_view, component_number, region_views, byte_limit, work_limit, initial_work,
                                ),
                                storage_context==(crate::specs::Part2NltComponentStorageContext {
                                    source:source_view,number:component_number,regions:region_views,
                                    maximum_bytes:byte_limit,maximum_work:work_limit,initial_work}),
                                crate::specs::part2_nlt_capacity_result(storage_context,crate::specs::Part2NltCapacityRole::Scratch,Ok(())),
                                crate::specs::part2_nlt_component_storage_result(storage_context,crate::specs::part2_nlt_component_mutation(
                                    source_view,component_number,region_views,byte_limit,work_limit,initial_work)),
                                component_expected == match region_goal {
                                    Err(error) => Err(error),
                                    Ok(state) => crate::specs::part2_nlt_finish_component(source_view, state, byte_limit),
                                },
                                region_goal == match rows_goal {
                                    Err(error) => Err(error),
                                    Ok(state) => crate::specs::part2_nlt_component_regions(
                                        source_view, component_number, region_views, region_index as nat + 1, work_limit, state,
                                    ),
                                },
                                rows_goal == match row_goal {
                                    Err(error) => Err(error),
                                    Ok(state) => crate::specs::part2_nlt_region_rows(source_view, region_view, (y + 1) as u32, work_limit, state),
                                },
                                row_goal == crate::specs::part2_nlt_region_row(
                                    source_view, region_view, y, x, work_limit, nlt_scratch_view(output@, target, work),
                                ),
                                decreases region.x1 - x,
                            )
                        )]
                    while x < region.x1 {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            reveal(crate::specs::part2_nlt_component_mutation);
                            reveal_with_fuel(crate::specs::part2_nlt_region_row, 1);
                        }
                        #[cfg(verus_keep_ghost)]
                        proof_decl! { let ghost before_pixel = output@; }
                        let index = index(self.width, x, y)?;
                        let decoded;
                        {
                            let slot = output.get_mut(index).ok_or_else(invalid_image)?;
                            if slot.is_some() {
                                return Err(invalid_transform());
                            }
                            let source = match &self.samples {
                                TypedSamples::Signed(samples) => {
                                    i128::from(*samples.get(index).ok_or_else(invalid_image)?)
                                }
                                TypedSamples::Unsigned(samples) => {
                                    i128::from(*samples.get(index).ok_or_else(invalid_image)?)
                                }
                            };
                            decoded = inverse_nlt_sample(source, source_info, region.transform)?;
                            *slot = Some(decoded);
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! { assert(output@ =~= before_pixel.update(index as int, Some(decoded))); }
                        charge_mct_work(&mut work, 1, limits)?;
                        x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
                    }
                    #[cfg(verus_keep_ghost)]
                    proof! { reveal_with_fuel(crate::specs::part2_nlt_region_row, 1); }
                    y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                #[cfg(verus_keep_ghost)]
                proof! { reveal_with_fuel(crate::specs::part2_nlt_region_rows, 1); }
            }
            region_index = region_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_nlt_component_regions, 1);
            assert(crate::specs::part2_nlt_component_region_state(storage_context)
                ==Ok(nlt_scratch_view(output@,target,work)));
            assert(component_expected == crate::specs::part2_nlt_finish_component(
                source_view, nlt_scratch_view(output@, target, work), byte_limit,
            ));
        }
        if let Some((precision, signed_output)) = target {
            validate_bytes(sample_count, 8, limits)?;
            if signed_output {
                let reserved = if sample_count == 0 {
                    Ok(Vec::new())
                } else {
                    crate::allocation::empty_with_capacity(sample_count)
                };
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_nlt_capacity_observed(storage_context,crate::specs::Part2NltCapacityRole::SignedSamples,
                        crate::allocation::inspection_capacity_outcome(reserved));
                    if let Err(error)=reserved {
                        crate::specs::part2_nlt_component_samples_refused(storage_context,nlt_scratch_view(output@,target,work),true,error);
                    }
                }
                let mut samples = reserved?;
                let mut index = 0_usize;
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost collected_goal = crate::specs::part2_nlt_collect_samples(
                        output@, true, 0, crate::specs::Part1TypedSampleSequence::Signed(Seq::empty()),
                    );
                }
                #[cfg_attr(
                        verus_keep_ghost,
                        verus_spec(
                            invariant index <= output.len(),
                            source_view == typed_component_view(old(self)),
                            initial_defs == typed_component_definitions(old(self)),
                            typed_component_view(self) == source_view,
                            self.channel_definitions@ == initial_defs,
                            region_views == crate::decode::nonlinear_regions_view(regions@),
                            byte_limit == crate::limits::resource_decoded_bytes_limit(limits),
                            work_limit == crate::limits::resource_work_limit(limits),
                            signed_output,
                            component_expected == crate::specs::part2_nlt_component(
                                source_view, component_number, region_views, byte_limit, work_limit, initial_work,
                            ),
                            storage_context==(crate::specs::Part2NltComponentStorageContext {
                                source:source_view,number:component_number,regions:region_views,
                                maximum_bytes:byte_limit,maximum_work:work_limit,initial_work}),
                            crate::specs::part2_nlt_component_storage_result(storage_context,crate::specs::part2_nlt_component_mutation(
                                source_view,component_number,region_views,byte_limit,work_limit,initial_work)),
                            component_expected == match collected_goal {
                                Err(error) => Err(error),
                                Ok(values) => Ok((crate::specs::part2_nlt_updated_component(source_view, precision, signed_output, values), work)),
                            },
                            collected_goal == crate::specs::part2_nlt_collect_samples(
                                output@, true, index as nat, crate::specs::Part1TypedSampleSequence::Signed(samples@),
                            ),
                            decreases output.len() - index,
                        )
                    )]
                while index < output.len() {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part2_nlt_component_mutation);
                        reveal_with_fuel(crate::specs::part2_nlt_collect_samples, 1);
                    }
                    let value = match output.get(index) {
                        Some(Some(value)) => *value,
                        _ => return Err(invalid_image()),
                    };
                    let value = match i64::try_from(value) {
                        Ok(value) => value,
                        Err(_) => return Err(invalid_image()),
                    };
                    samples.push(value);
                    index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                #[cfg(verus_keep_ghost)]
                proof! { reveal_with_fuel(crate::specs::part2_nlt_collect_samples, 1); }
                self.samples = TypedSamples::Signed(samples);
            } else {
                let reserved = if sample_count == 0 {
                    Ok(Vec::new())
                } else {
                    crate::allocation::empty_with_capacity(sample_count)
                };
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_nlt_capacity_observed(storage_context,crate::specs::Part2NltCapacityRole::UnsignedSamples,
                        crate::allocation::inspection_capacity_outcome(reserved));
                    if let Err(error)=reserved {
                        crate::specs::part2_nlt_component_samples_refused(storage_context,nlt_scratch_view(output@,target,work),false,error);
                    }
                }
                let mut samples = reserved?;
                let mut index = 0_usize;
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost collected_goal = crate::specs::part2_nlt_collect_samples(
                        output@, false, 0, crate::specs::Part1TypedSampleSequence::Unsigned(Seq::empty()),
                    );
                }
                #[cfg_attr(
                        verus_keep_ghost,
                        verus_spec(
                            invariant index <= output.len(),
                            source_view == typed_component_view(old(self)),
                            initial_defs == typed_component_definitions(old(self)),
                            typed_component_view(self) == source_view,
                            self.channel_definitions@ == initial_defs,
                            region_views == crate::decode::nonlinear_regions_view(regions@),
                            byte_limit == crate::limits::resource_decoded_bytes_limit(limits),
                            work_limit == crate::limits::resource_work_limit(limits),
                            !signed_output,
                            component_expected == crate::specs::part2_nlt_component(
                                source_view, component_number, region_views, byte_limit, work_limit, initial_work,
                            ),
                            storage_context==(crate::specs::Part2NltComponentStorageContext {
                                source:source_view,number:component_number,regions:region_views,
                                maximum_bytes:byte_limit,maximum_work:work_limit,initial_work}),
                            crate::specs::part2_nlt_component_storage_result(storage_context,crate::specs::part2_nlt_component_mutation(
                                source_view,component_number,region_views,byte_limit,work_limit,initial_work)),
                            component_expected == match collected_goal {
                                Err(error) => Err(error),
                                Ok(values) => Ok((crate::specs::part2_nlt_updated_component(source_view, precision, signed_output, values), work)),
                            },
                            collected_goal == crate::specs::part2_nlt_collect_samples(
                                output@, false, index as nat, crate::specs::Part1TypedSampleSequence::Unsigned(samples@),
                            ),
                            decreases output.len() - index,
                        )
                    )]
                while index < output.len() {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part2_nlt_component_mutation);
                        reveal_with_fuel(crate::specs::part2_nlt_collect_samples, 1);
                    }
                    let value = match output.get(index) {
                        Some(Some(value)) => *value,
                        _ => return Err(invalid_image()),
                    };
                    let value = match u64::try_from(value) {
                        Ok(value) => value,
                        Err(_) => return Err(invalid_image()),
                    };
                    samples.push(value);
                    index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                #[cfg(verus_keep_ghost)]
                proof! { reveal_with_fuel(crate::specs::part2_nlt_collect_samples, 1); }
                self.samples = TypedSamples::Unsigned(samples);
            }
            self.info.precision = precision;
            self.info.signed = signed_output;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(component_expected == Ok((typed_component_view(self), work))); }
        Ok(work)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_copy_result(Seq::new(count as nat,|_:int|None::<i128>),result),
        count==0 ==> result.is_ok(),
))]
fn nlt_scratch_values(count: usize) -> Result<Vec<Option<i128>>, DecodeError> {
    let mut values = if count == 0 {
        Vec::new()
    } else {
        crate::allocation::empty_with_capacity(count)?
    };
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant values.len()<=count,forall|index:int|0<=index<values.len() ==> values@[index]==None::<i128>,
        decreases count-values.len(),
    ))]
    while values.len() < count {
        values.push(None);
    }
    #[cfg(verus_keep_ghost)]
    proof! {assert(values@ =~= Seq::new(count as nat,|_:int|None::<i128>));}
    Ok(values)
}

impl TypedImage {
    #[cfg(test)]
    pub(crate) fn apply_nonlinear_transforms(
        &mut self,
        extensions: &Part2Extensions,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        let mut work = 0_u64;
        let mut component_index = 0_usize;
        while component_index < self.components.len() {
            let component_number =
                u16::try_from(component_index).map_err(|_| arithmetic_overflow())?;
            let Some(transform) = extensions.nonlinear_transform_for(component_number) else {
                component_index = component_index
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
                continue;
            };
            let component = self
                .components
                .get_mut(component_index)
                .ok_or_else(invalid_image)?;
            let source_info = component.info;
            if source_info.precision == 0
                || source_info.precision > 38
                || transform.precision() == 0
                || transform.precision() > 38
            {
                return Err(invalid_image());
            }
            let sample_count = match &component.samples {
                TypedSamples::Signed(samples) => samples.len(),
                TypedSamples::Unsigned(samples) => samples.len(),
            };
            work = work
                .checked_add(sample_count as u64)
                .ok_or_else(arithmetic_overflow)?;
            if work > limits.maximum_work_units() {
                return Err(DecodeError::limit(
                    Resource::WorkUnits,
                    limits.maximum_work_units(),
                    work,
                ));
            }
            validate_bytes(sample_count, 8, limits)?;
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint()?;
            let mut output = Vec::with_capacity(sample_count);
            let mut sample_index = 0_usize;
            while sample_index < sample_count {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(sample_index)?;
                let source = match &component.samples {
                    TypedSamples::Signed(samples) => {
                        i128::from(*samples.get(sample_index).ok_or_else(invalid_image)?)
                    }
                    TypedSamples::Unsigned(samples) => {
                        i128::from(*samples.get(sample_index).ok_or_else(invalid_image)?)
                    }
                };
                output.push(inverse_nlt_sample(source, source_info, transform)?);
                sample_index = sample_index
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }
            component.samples = if transform.signed() {
                let mut signed = Vec::with_capacity(output.len());
                let mut index = 0_usize;
                while index < output.len() {
                    signed.push(
                        i64::try_from(*output.get(index).ok_or_else(invalid_image)?)
                            .map_err(|_| invalid_image())?,
                    );
                    index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                TypedSamples::Signed(signed)
            } else {
                let mut unsigned = Vec::with_capacity(output.len());
                let mut index = 0_usize;
                while index < output.len() {
                    unsigned.push(
                        u64::try_from(*output.get(index).ok_or_else(invalid_image)?)
                            .map_err(|_| invalid_image())?,
                    );
                    index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                TypedSamples::Unsigned(unsigned)
            };
            component.info.precision = transform.precision();
            component.info.signed = transform.signed();
            component_index = component_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        Ok(())
    }
}
