//! Layer and composition inspection and public metadata accessors.
use super::resources::{arithmetic_overflow, invalid_layer, registered_extent};
use super::timeline::build_timeline;
use super::{
    DecodeError, Jp2File, JpxCompositionInfo, JpxFrameInfo, JpxInspection, JpxInstructionInfo,
    JpxLayerInfo, MalformedKind, ResourceLimits, jp2,
};
#[cfg(verus_keep_ghost)]
use super::{
    composition_source_frames, composition_source_view, inspection_composition_reference,
    instruction_source_layer_index,
};
#[cfg(verus_keep_ghost)]
use super::{
    frame_views, inspected_layer_view, inspected_layers_view, inspection_file_input,
    inspection_layer_config, inspection_result, inspection_source_geometries, timeline_set_views,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl JpxLayerInfo {
    pub const fn index(&self) -> usize {
        self.index
    }

    pub fn codestream_indices(&self) -> &[u16] {
        &self.codestream_indices
    }

    pub const fn horizontal_grid_size(&self) -> u16 {
        self.horizontal_grid_size
    }

    pub const fn vertical_grid_size(&self) -> u16 {
        self.vertical_grid_size
    }

    pub const fn horizontal_offset(&self) -> u32 {
        self.horizontal_offset
    }

    pub const fn vertical_offset(&self) -> u32 {
        self.vertical_offset
    }

    pub const fn width(&self) -> u32 {
        self.width
    }

    pub const fn height(&self) -> u32 {
        self.height
    }

    pub const fn has_color_group(&self) -> bool {
        self.has_color_group
    }

    pub const fn has_opacity_box(&self) -> bool {
        self.has_opacity_box
    }

    pub const fn nested_metadata_boxes(&self) -> u32 {
        self.nested_metadata_boxes
    }
}

impl JpxCompositionInfo {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == composition_source_view(self).0,))]
    pub const fn width(&self) -> u32 {
        self.width
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == composition_source_view(self).1,))]
    pub const fn height(&self) -> u32 {
        self.height
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == composition_source_view(self).2,))]
    pub const fn loop_count(&self) -> u8 {
        self.loop_count
    }

    pub const fn instruction_sets(&self) -> u32 {
        self.instruction_sets
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == composition_source_frames(self),
    ))]
    pub fn frames(&self) -> &[JpxFrameInfo] {
        &self.frames
    }

    pub const fn total_duration_milliseconds(&self) -> u64 {
        self.total_duration_milliseconds
    }

    pub const fn has_unknown_boxes(&self) -> bool {
        self.has_unknown_boxes
    }
}

impl JpxFrameInfo {
    pub const fn index(&self) -> usize {
        self.index
    }

    pub const fn duration_milliseconds(&self) -> u32 {
        self.duration_milliseconds
    }

    pub const fn start_milliseconds(&self) -> u64 {
        self.start_milliseconds
    }

    pub const fn persistent(&self) -> bool {
        self.persistent
    }

    pub fn instructions(&self) -> &[JpxInstructionInfo] {
        &self.instructions
    }
}

impl JpxInstructionInfo {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == instruction_source_layer_index(self),))]
    pub const fn layer_index(&self) -> usize {
        self.layer_index
    }

    pub const fn target_x(&self) -> u32 {
        self.target_x
    }

    pub const fn target_y(&self) -> u32 {
        self.target_y
    }

    pub const fn target_width(&self) -> u32 {
        self.target_width
    }

    pub const fn target_height(&self) -> u32 {
        self.target_height
    }

    pub const fn source_region(&self) -> (u32, u32, u32, u32) {
        (
            self.source_x,
            self.source_y,
            self.source_width,
            self.source_height,
        )
    }

    pub const fn persistent(&self) -> bool {
        self.persistent
    }

    pub const fn next_reuse(&self) -> u32 {
        self.next_reuse
    }
}

impl JpxInspection {
    pub fn layers(&self) -> &[JpxLayerInfo] {
        &self.layers
    }

    pub fn layer(&self, index: usize) -> Result<&JpxLayerInfo, DecodeError> {
        self.layers
            .get(index)
            .ok_or(DecodeError::LayerIndexOutOfRange {
                index,
                layers: self.layers.len(),
            })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == inspection_composition_reference(self),
    ))]
    pub const fn composition(&self) -> Option<&JpxCompositionInfo> {
        self.composition.as_ref()
    }

    pub const fn metadata_boxes(&self) -> u32 {
        self.metadata_boxes
    }

    pub const fn metadata_depth(&self) -> u32 {
        self.metadata_depth
    }
}

pub fn inspect_jpx_layers(
    input: &[u8],
    limits: &ResourceLimits,
) -> Result<JpxInspection, DecodeError> {
    let inspected = jp2::parse_and_inspect(input, limits)?;
    ensure_jpx(inspected.file())?;
    inspect_file(inspected.file(), inspected.codestreams(), limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures inspection_result(result) == crate::specs::part2_inspect_jpx_file(
        inspection_file_input(file), inspection_source_geometries(codestreams@),
        crate::limits::resource_frame_limit(limits)),
))]
pub(super) fn inspect_file(
    file: &Jp2File<'_>,
    codestreams: &[crate::codestream::CodestreamInfo],
    limits: &ResourceLimits,
) -> Result<JpxInspection, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = inspection_file_input(file);
        let ghost geometries = inspection_source_geometries(codestreams@);
        let ghost maximum_frames = crate::limits::resource_frame_limit(limits);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_inspect_jpx_file);
        reveal(crate::specs::part2_inspection_layers_prefix);
    }
    let layer_count = effective_layer_count(file);
    let mut layers = Vec::with_capacity(layer_count);
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! { assert(inspected_layers_view(layers@) =~= Seq::empty()); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= layer_count,
                layers.len() == index,
                layer_count == crate::specs::part2_inspection_layer_count(input),
                input == inspection_file_input(file),
                geometries == inspection_source_geometries(codestreams@),
                maximum_frames == crate::limits::resource_frame_limit(limits),
                crate::specs::part2_inspection_layers_prefix(input, geometries, index as nat)
                    == Ok(inspected_layers_view(layers@)),
            decreases layer_count - index,
        )
    )]
    while index < layer_count {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = inspected_layers_view(layers@); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_inspect_jpx_file);
            reveal(crate::specs::part2_inspection_layer);
            crate::specs::part2_inspection_layers_step(input, geometries, index as nat);
            crate::specs::part2_inspection_layers_error(input, geometries, index as nat + 1, layer_count as nat);
        }
        let mut codestream_indices = Vec::new();
        if file.compositing_layers().is_empty() {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(input.layers.len() == 0);
                assert(index as nat > u16::MAX as nat ==>
                    crate::specs::part2_inspection_layer(input, geometries, index)
                        == Err(crate::specs::part2_composition_error(true)));
            }
            let source = u16::try_from(index).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_composition_error(true),
                ))]
                |_error| arithmetic_overflow(),
            )?;
            codestream_indices.push(source);
            let codestream = codestreams.get(index).ok_or_else(invalid_layer)?;
            layers.push(JpxLayerInfo {
                index,
                codestream_indices,
                horizontal_grid_size: 1,
                vertical_grid_size: 1,
                horizontal_offset: 0,
                vertical_offset: 0,
                width: codestream.image_size.width,
                height: codestream.image_size.height,
                has_color_group: false,
                has_opacity_box: false,
                nested_metadata_boxes: 0,
            });
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_inspection_layer(input, geometries, index)
                    == Ok(inspected_layer_view(&layers@[index as int])));
                assert(inspected_layers_view(layers@)
                    =~= previous.push(inspected_layer_view(&layers@[index as int])));
            }
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            continue;
        }
        #[cfg(verus_keep_ghost)]
        proof! { jp2::source_layer_reference_known(file, index); }
        let layer = file.compositing_layer(index)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost config = inspection_layer_config(layer); }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(index < input.layers.len());
            assert(config == input.layers[index as int]);
        }
        let (horizontal_offset, vertical_offset, width, height) = if layer
            .registrations()
            .is_empty()
        {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(index as nat > u16::MAX as nat ==>
                    crate::specs::part2_inspection_layer(input, geometries, index)
                        == Err(crate::specs::part2_composition_error(true)));
            }
            let source = u16::try_from(index).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_composition_error(true),
                    ))]
                |_error| arithmetic_overflow(),
            )?;
            codestream_indices.push(source);
            let codestream = codestreams.get(index).ok_or_else(invalid_layer)?;
            (
                0,
                0,
                codestream.image_size.width,
                codestream.image_size.height,
            )
        } else {
            let mut registration_index = 0_usize;
            let registration_count = layer.registrations().len();
            let mut width = u32::MAX;
            let mut height = u32::MAX;
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_inspection_registration_prefix);
                assert(codestream_indices@ =~= Seq::empty());
            }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant registration_index <= registration_count,
                        registration_count == config.registrations.len(),
                        config == inspection_layer_config(layer),
                        index < input.layers.len(),
                        index < layer_count, layer_count == crate::specs::part2_inspection_layer_count(input),
                        layers.len() == index,
                        input == inspection_file_input(file),
                        config == input.layers[index as int],
                        geometries == inspection_source_geometries(codestreams@),
                        maximum_frames == crate::limits::resource_frame_limit(limits),
                        crate::specs::part2_inspection_layers_prefix(input, geometries, index as nat)
                            == Ok(inspected_layers_view(layers@)),
                        crate::specs::part2_inspection_registration_prefix(config, geometries, registration_index as nat)
                            == Ok((codestream_indices@, width, height)),
                    decreases registration_count - registration_index,
                )
            )]
            while registration_index < registration_count {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_inspect_jpx_file);
                    reveal(crate::specs::part2_inspection_layer);
                    reveal(crate::specs::part2_inspection_registration_step);
                    crate::specs::part2_inspection_layers_step(input, geometries, index as nat);
                    crate::specs::part2_inspection_layers_error(input, geometries, index as nat + 1, layer_count as nat);
                    crate::specs::part2_inspection_registrations_step(config, geometries, registration_index as nat);
                    crate::specs::part2_inspection_registrations_error(
                        config, geometries, registration_index as nat + 1, registration_count as nat);
                }
                let registration = layer
                    .registrations()
                    .get(registration_index)
                    .ok_or_else(arithmetic_overflow)?;
                codestream_indices.push(registration.codestream_index);
                let codestream = codestreams
                    .get(usize::from(registration.codestream_index))
                    .ok_or_else(invalid_layer)?;
                width = width.min(registered_extent(
                    codestream.image_size.width,
                    u32::from(registration.horizontal_subsampling),
                    u32::from(layer.horizontal_grid_size()),
                    registration.horizontal_offset,
                )?);
                height = height.min(registered_extent(
                    codestream.image_size.height,
                    u32::from(registration.vertical_subsampling),
                    u32::from(layer.vertical_grid_size()),
                    registration.vertical_offset,
                )?);
                registration_index = registration_index
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }
            (0, 0, width, height)
        };
        layers.push(JpxLayerInfo {
            index,
            codestream_indices,
            horizontal_grid_size: layer.horizontal_grid_size(),
            vertical_grid_size: layer.vertical_grid_size(),
            horizontal_offset,
            vertical_offset,
            width,
            height,
            has_color_group: layer.has_color_group(),
            has_opacity_box: layer.has_opacity_box(),
            nested_metadata_boxes: layer.nested_metadata_boxes(),
        });
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_inspection_layer(input, geometries, index)
                == Ok(inspected_layer_view(&layers@[index as int])));
            assert(inspected_layers_view(layers@)
                =~= previous.push(inspected_layer_view(&layers@[index as int])));
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_inspection_composition); }
    let composition = match file.composition() {
        Some(composition) => {
            let frames = build_timeline(
                composition,
                effective_layer_count(file),
                limits.maximum_frames(),
            )?;
            let mut total_duration_milliseconds = 0_u64;
            let mut frame_index = 0_usize;
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_inspection_duration_prefix); }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant frame_index <= frames.len(),
                        input == inspection_file_input(file),
                        geometries == inspection_source_geometries(codestreams@),
                        maximum_frames == crate::limits::resource_frame_limit(limits),
                        layer_count == crate::specs::part2_inspection_layer_count(input),
                        crate::specs::part2_inspection_layers_prefix(input, geometries, layer_count as nat)
                            == Ok(inspected_layers_view(layers@)),
                        input.composition.is_some(),
                        input.composition.unwrap().sets == timeline_set_views(composition),
                        crate::specs::part2_build_timeline(input.composition.unwrap().sets, layer_count, maximum_frames)
                            == Ok(frame_views(frames@)),
                        crate::specs::part2_inspection_duration_prefix(frame_views(frames@), frame_index as nat)
                            == Ok(total_duration_milliseconds),
                    decreases frames.len() - frame_index,
                )
            )]
            while frame_index < frames.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_inspect_jpx_file);
                    reveal(crate::specs::part2_inspection_composition);
                    crate::specs::part2_inspection_durations_step(frame_views(frames@), frame_index as nat);
                    crate::specs::part2_inspection_durations_error(
                        frame_views(frames@), frame_index as nat + 1, frames.len() as nat);
                }
                total_duration_milliseconds = total_duration_milliseconds
                    .checked_add(u64::from(
                        frames
                            .get(frame_index)
                            .ok_or_else(arithmetic_overflow)?
                            .duration_milliseconds,
                    ))
                    .ok_or_else(arithmetic_overflow)?;
                frame_index = frame_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_inspect_jpx_file);
                reveal(crate::specs::part2_inspection_composition);
            }
            Some(JpxCompositionInfo {
                width: composition.width,
                height: composition.height,
                loop_count: composition.loop_count,
                instruction_sets: u32::try_from(composition.instruction_sets.len()).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_composition_error(true),
                        ))]
                    |_error| arithmetic_overflow(),
                )?,
                frames,
                total_duration_milliseconds,
                has_unknown_boxes: composition.has_unknown_boxes,
            })
        }
        None => None,
    };
    Ok(JpxInspection {
        layers,
        composition,
        metadata_boxes: file.metadata_boxes(),
        metadata_depth: file.metadata_depth(),
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == if crate::specs::part2_file_type_jpx(jp2::jpx_file_decode_view(file).0) {
        Ok(())
    } else { Err(DecodeError::MalformedInput { offset: 0, kind: MalformedKind::InvalidProfile }) },
))]
pub(super) fn ensure_jpx(file: &Jp2File<'_>) -> Result<(), DecodeError> {
    if file.file_type().is_jpx_compatible() {
        Ok(())
    } else {
        Err(DecodeError::malformed(0, MalformedKind::InvalidProfile))
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::effective_jpx_layer_count(
        jp2::source_file_layers(file).len(), jp2::jpx_file_decode_view(file).1.len()),
))]
pub(super) fn effective_layer_count(file: &Jp2File<'_>) -> usize {
    crate::refinement::effective_layer_count(
        file.compositing_layers().len(),
        file.codestream_count(),
    )
}
