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

pub(super) fn inspect_file(
    file: &Jp2File<'_>,
    codestreams: &[crate::codestream::CodestreamInfo],
    limits: &ResourceLimits,
) -> Result<JpxInspection, DecodeError> {
    let layer_count = effective_layer_count(file);
    let mut layers = Vec::with_capacity(layer_count);
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= layer_count,
            decreases layer_count - index,
        )
    )]
    while index < layer_count {
        let mut codestream_indices = Vec::new();
        if file.compositing_layers().is_empty() {
            let source = u16::try_from(index).map_err(|_| arithmetic_overflow())?;
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
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            continue;
        }
        let layer = file.compositing_layer(index)?;
        let (horizontal_offset, vertical_offset, width, height) =
            if layer.registrations().is_empty() {
                let source = u16::try_from(index).map_err(|_| arithmetic_overflow())?;
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
                #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant registration_index <= registration_count,
                    decreases registration_count - registration_index,
                )
            )]
                while registration_index < registration_count {
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
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let composition = match file.composition() {
        Some(composition) => {
            let frames = build_timeline(
                composition,
                effective_layer_count(file),
                limits.maximum_frames(),
            )?;
            let mut total_duration_milliseconds = 0_u64;
            let mut frame_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant frame_index <= frames.len(),
                    decreases frames.len() - frame_index,
                )
            )]
            while frame_index < frames.len() {
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
            Some(JpxCompositionInfo {
                width: composition.width,
                height: composition.height,
                loop_count: composition.loop_count,
                instruction_sets: u32::try_from(composition.instruction_sets.len())
                    .map_err(|_| arithmetic_overflow())?,
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

pub(super) fn ensure_jpx(file: &Jp2File<'_>) -> Result<(), DecodeError> {
    if file.file_type().is_jpx_compatible() {
        Ok(())
    } else {
        Err(DecodeError::malformed(0, MalformedKind::InvalidProfile))
    }
}

pub(super) fn effective_layer_count(file: &Jp2File<'_>) -> usize {
    crate::refinement::effective_layer_count(
        file.compositing_layers().len(),
        file.codestream_count(),
    )
}
