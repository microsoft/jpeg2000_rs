use super::geometry::{arithmetic_overflow, checked_area, invalid_color_input};
use super::{ConvertedChannel, ConvertedImage};
#[cfg(test)]
use super::{ConvertedChannelType, ConvertedColorSpace};
#[cfg(verus_keep_ghost)]
use super::{
    converted_channel_views, converted_channel_views_push, converted_image_model,
    converted_image_result, normalized_plane_result,
};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl ConvertedImage {
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures crate::specs::part2_color_crop_storage_result(crate::specs::Part2ColorCropContext {
                image:converted_image_model(&self),x,y,width,height,
            },converted_image_result(result)),
            result!=Err(DecodeError::AllocationFailed) ==> converted_image_result(result) == crate::specs::color_crop_image(
                converted_image_model(&self), x, y, width, height,
            ),
        )
    )]
    pub(crate) fn crop(self, x: u32, y: u32, width: u32, height: u32) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost input = converted_image_model(&self); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost storage_context=crate::specs::Part2ColorCropContext {image:input,x,y,width,height};}
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_color_crop_storage_normal(storage_context);}
        if width == 0 || height == 0 {
            return Err(invalid_color_input());
        }
        let x1 = x.checked_add(width).ok_or_else(arithmetic_overflow)?;
        let y1 = y.checked_add(height).ok_or_else(arithmetic_overflow)?;
        if x1 > self.width || y1 > self.height {
            return Err(invalid_color_input());
        }
        if x == 0 && y == 0 && width == self.width && height == self.height {
            return Ok(self);
        }
        let count = checked_area(width, height)?;
        let allocated = if self.channels.is_empty() {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(self.channels.len())
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_color_output_capacity_observed(crate::specs::Part2ColorOutputCapacity::CropChannels {context:storage_context},
                crate::allocation::inspection_capacity_outcome(allocated));
            if let Err(error)=allocated {crate::specs::part2_color_crop_storage_owner_refused(storage_context,error);}
        }
        let mut channels = allocated?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::proofs::internal_specs::color_crop_ready(input, x, y, width, height, x1, y1, count));
            crate::proofs::production_impl::production_crop_channels_empty(input.4, input.0, x, y, x1, y1);
            assert(converted_channel_views(channels@) =~= Seq::<crate::specs::ColorChannelModel>::empty());
        }
        let mut channel_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant channel_index <= self.channels.len(),
                    storage_context==(crate::specs::Part2ColorCropContext {image:input,x,y,width,height}),
                    crate::specs::part2_color_crop_storage_result(storage_context,crate::specs::part2_color_crop_value(storage_context)),
                    input == converted_image_model(&self),
                    crate::proofs::internal_specs::color_crop_ready(input, x, y, width, height, x1, y1, count),
                    crate::specs::color_crop_channels(input.4, input.0, x, y, x1, y1, channel_index as nat)
                        == Ok(converted_channel_views(channels@)),
                decreases self.channels.len() - channel_index,
            )
        )]
        while channel_index < self.channels.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_crop_channels_step(input.4, input.0, x, y, x1, y1, channel_index as nat);
            }
            let channel = self
                .channels
                .get(channel_index)
                .ok_or_else(invalid_color_input)?;
            let samples = match crop_plane(&channel.samples, self.width, x, y, x1, y1, count) {
                Ok(samples) => samples,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        if crate::specs::color_crop_plane(input.4[channel_index as int].1,input.0,x,y,x1,y1)==Err(error) {
                            crate::proofs::production_impl::production_crop_channels_error(
                                input.4, input.0, x, y, x1, y1, channel_index as nat + 1, input.4.len(), error,
                            );
                        }
                        crate::specs::part2_color_crop_storage_plane_error(storage_context,channel_index as nat,count,error);
                    }
                    return Err(error);
                }
            };
            let output = ConvertedChannel {
                channel_type: channel.channel_type,
                samples,
            };
            #[cfg(verus_keep_ghost)]
            proof! { converted_channel_views_push(channels@, output); }
            channels.push(output);
            channel_index = channel_index
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        Ok(Self {
            width,
            height,
            color_space: self.color_space,
            precision: self.precision,
            channels,
        })
    }

    #[cfg(test)]
    pub(crate) fn from_test_channels(
        width: u32,
        height: u32,
        color_space: ConvertedColorSpace,
        channels: Vec<(ConvertedChannelType, Vec<u16>)>,
    ) -> Self {
        Self {
            width,
            height,
            color_space,
            precision: 16,
            channels: channels
                .into_iter()
                .map(|(channel_type, samples)| ConvertedChannel {
                    channel_type,
                    samples,
                })
                .collect(),
        }
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires x <= x1, y <= y1,
        ensures crate::specs::part2_color_crop_plane_storage_result(input@,source_width,x,y,x1,y1,count,normalized_plane_result(result)),
        result!=Err(DecodeError::AllocationFailed) ==> normalized_plane_result(result) == crate::specs::color_crop_plane(input@, source_width, x, y, x1, y1),
    )
)]
fn crop_plane(
    input: &[u16],
    source_width: u32,
    x: u32,
    y: u32,
    x1: u32,
    y1: u32,
    count: usize,
) -> Result<Vec<u16>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_color_crop_plane_storage_normal(input@,source_width,x,y,x1,y1,count);}
    let allocated = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_color_output_capacity_observed(crate::specs::part2_color_crop_plane_request(input@,source_width,x,y,x1,y1,count),
            crate::allocation::inspection_capacity_outcome(allocated));
        if let Err(error)=allocated {crate::specs::part2_color_crop_plane_storage_refused(input@,source_width,x,y,x1,y1,count,error);}
    }
    let mut samples = allocated?;
    let mut row = y;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_crop_rows_empty(input@, source_width, x, y, (x1 - x) as u32);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant y <= row <= y1, x <= x1,
                crate::specs::part2_color_crop_plane_storage_result(input@,source_width,x,y,x1,y1,count,
                    crate::specs::color_crop_plane(input@,source_width,x,y,x1,y1)),
                crate::specs::color_crop_rows(input@, source_width, x, y, (x1 - x) as u32, (row - y) as nat)
                    == Ok(samples@),
            decreases y1 - row,
        )
    )]
    while row < y1 {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = samples@; }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_crop_columns_empty(input@, source_width, row, x, initial);
        }
        let mut column = x;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant x <= column <= x1, y <= row < y1,
                    crate::specs::part2_color_crop_plane_storage_result(input@,source_width,x,y,x1,y1,count,
                        crate::specs::color_crop_plane(input@,source_width,x,y,x1,y1)),
                    crate::specs::color_crop_rows(input@, source_width, x, y, (x1 - x) as u32, (row - y) as nat)
                        == Ok(initial),
                    crate::specs::color_crop_columns(input@, source_width, row, x, initial, (column - x) as nat)
                        == Ok(samples@),
                decreases x1 - column,
            )
        )]
        while column < x1 {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_crop_columns_step(
                    input@, source_width, row, x, initial, (column - x) as nat,
                );
            }
            let value = match crop_sample(input, source_width, row, column) {
                Ok(value) => value,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_crop_columns_error(
                            input@, source_width, row, x, initial, (column - x) as nat + 1, (x1 - x) as nat, error,
                        );
                        crate::proofs::production_impl::production_crop_rows_step(
                            input@, source_width, x, y, (x1 - x) as u32, (row - y) as nat,
                        );
                        crate::proofs::production_impl::production_crop_rows_error(
                            input@, source_width, x, y, (x1 - x) as u32,
                            (row - y) as nat + 1, (y1 - y) as nat, error,
                        );
                    }
                    return Err(error);
                }
            };
            samples.push(value);
            column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_crop_rows_step(
                input@, source_width, x, y, (x1 - x) as u32, (row - y) as nat,
            );
        }
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(samples)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_crop_sample(input@, source_width, row, column),
    )
)]
fn crop_sample(
    input: &[u16],
    source_width: u32,
    row: u32,
    column: u32,
) -> Result<u16, DecodeError> {
    let offset = (row as usize)
        .checked_mul(source_width as usize)
        .ok_or_else(arithmetic_overflow)?;
    let index = offset
        .checked_add(column as usize)
        .ok_or_else(arithmetic_overflow)?;
    Ok(*input.get(index).ok_or_else(invalid_color_input)?)
}
