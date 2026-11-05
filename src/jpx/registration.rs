//! Layer registration geometry and registered sample copying.
use super::resources::{
    arithmetic_overflow, checked_area, index_of, invalid_layer, registered_extent,
};
use super::{DecodeError, OwnedLayer, jp2};
#[cfg(verus_keep_ghost)]
use super::{layer_registration_view, owned_layer_outcome, owned_layer_view};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::normalized_plane_result(result) == crate::specs::part2_register_component_plane(
        crate::specs::Part2PlaneRegistration {
            source: source@, source_width, source_height, width, height,
            horizontal_subsampling, vertical_subsampling, horizontal_grid, vertical_grid,
            horizontal_offset, vertical_offset,
        }),
))]
pub(super) fn register_samples(
    source: &[u16],
    source_width: u32,
    source_height: u32,
    width: u32,
    height: u32,
    horizontal_subsampling: u32,
    vertical_subsampling: u32,
    horizontal_grid: u32,
    vertical_grid: u32,
    horizontal_offset: u32,
    vertical_offset: u32,
) -> Result<Vec<u16>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context = crate::specs::Part2PlaneRegistration {
            source: source@, source_width, source_height, width, height,
            horizontal_subsampling, vertical_subsampling, horizontal_grid, vertical_grid,
            horizontal_offset, vertical_offset,
        };
    }
    if source.len() != checked_area(source_width, source_height)?
        || horizontal_subsampling == 0
        || vertical_subsampling == 0
        || horizontal_grid == 0
        || vertical_grid == 0
    {
        return Err(invalid_layer());
    }
    let mut output = vec![0_u16; checked_area(width, height)?];
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = output@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_plane_registration_rows);
        assert(initial =~= Seq::new(output.len() as nat, |_index: int| 0u16));
    }
    let mut y = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant y <= height && vertical_subsampling > 0 && vertical_grid > 0,
                horizontal_subsampling > 0, horizontal_grid > 0,
                context == (crate::specs::Part2PlaneRegistration {
                    source: source@, source_width, source_height, width, height,
                    horizontal_subsampling, vertical_subsampling, horizontal_grid, vertical_grid,
                    horizontal_offset, vertical_offset,
                }),
                crate::specs::part2_layer_area(source_width, source_height) == Ok(source.len()),
                crate::specs::part2_layer_area(width, height) == Ok(output.len()),
                initial == Seq::new(output.len() as nat, |_index: int| 0u16),
                crate::specs::part2_plane_registration_rows(context, initial, y as nat) == Ok(output@),
            decreases height - y,
        )
    )]
    while y < height {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_plane_rows_step(context, initial, y as nat);
            if y as nat * vertical_grid as nat > u32::MAX as nat {
                assert(crate::specs::part2_plane_registration_rows(context, initial, y as nat + 1)
                    == Err(crate::specs::part2_composition_error(true)));
                crate::specs::part2_plane_rows_error(context, initial, y as nat + 1, height as nat,
                    crate::specs::part2_composition_error(true));
            }
        }
        let source_y_numerator = y
            .checked_mul(vertical_grid)
            .ok_or_else(arithmetic_overflow)?;
        if source_y_numerator >= vertical_offset {
            let source_y = crate::refinement::registered_source_coordinate(
                source_y_numerator,
                vertical_offset,
                vertical_subsampling,
            );
            if source_y < source_height {
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost row_initial = output@; }
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_plane_registration_columns); }
                let mut x = 0_u32;
                if horizontal_subsampling == 0 || horizontal_grid == 0 {
                    return Err(invalid_layer());
                }
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant x <= width && horizontal_subsampling > 0 && horizontal_grid > 0,
                            y < height, source_y < source_height,
                            vertical_subsampling > 0, vertical_grid > 0,
                            context == (crate::specs::Part2PlaneRegistration {
                                source: source@, source_width, source_height, width, height,
                                horizontal_subsampling, vertical_subsampling, horizontal_grid, vertical_grid,
                                horizontal_offset, vertical_offset,
                            }),
                            crate::specs::part2_layer_area(source_width, source_height) == Ok(source.len()),
                            crate::specs::part2_layer_area(width, height) == Ok(output.len()),
                            initial == Seq::new(output.len() as nat, |_index: int| 0u16),
                            crate::specs::part2_plane_registration_rows(context, initial, y as nat) == Ok(row_initial),
                            crate::specs::part2_plane_registration_rows(context, initial, y as nat + 1)
                                == crate::specs::part2_plane_registration_columns(context, y, source_y, row_initial, width as nat),
                            crate::specs::part2_plane_registration_columns(context, y, source_y, row_initial, x as nat) == Ok(output@),
                        decreases width - x,
                    )
                )]
                while x < width {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::specs::part2_plane_columns_step(context, y, source_y, row_initial, x as nat);
                        if x as nat * horizontal_grid as nat > u32::MAX as nat {
                            assert(crate::specs::part2_plane_registration_columns(context, y, source_y, row_initial, x as nat + 1)
                                == Err(crate::specs::part2_composition_error(true)));
                            crate::specs::part2_plane_columns_error(context, y, source_y, row_initial,
                                x as nat + 1, width as nat, crate::specs::part2_composition_error(true));
                            crate::specs::part2_plane_rows_error(context, initial, y as nat + 1, height as nat,
                                crate::specs::part2_composition_error(true));
                        }
                    }
                    let source_x_numerator = x
                        .checked_mul(horizontal_grid)
                        .ok_or_else(arithmetic_overflow)?;
                    if source_x_numerator >= horizontal_offset {
                        let source_x = crate::refinement::registered_source_coordinate(
                            source_x_numerator,
                            horizontal_offset,
                            horizontal_subsampling,
                        );
                        if source_x < source_width {
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                crate::specs::part2_plane_index_bound(width, height, x, y, output.len());
                                crate::specs::part2_plane_index_bound(
                                    source_width, source_height, source_x, source_y, source.len());
                            }
                            let destination = index_of(width, x, y)?;
                            *output.get_mut(destination).ok_or_else(invalid_layer)? = *source
                                .get(index_of(source_width, source_x, source_y)?)
                                .ok_or_else(invalid_layer)?;
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(crate::specs::part2_plane_registration_columns(
                                context, y, source_y, row_initial, x as nat + 1) == Ok(output@));
                        }
                    }
                    x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
            }
        }
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(output)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_registered_layer_geometry(
            source_width, source_height, layer_registration_view(registration), horizontal_grid_size, vertical_grid_size),
    )
)]
pub(super) fn registered_layer_geometry(
    source_width: u32,
    source_height: u32,
    registration: &jp2::CodestreamRegistration,
    horizontal_grid_size: u16,
    vertical_grid_size: u16,
) -> Result<(u32, u32, usize), DecodeError> {
    let horizontal_subsampling = u32::from(registration.horizontal_subsampling);
    let vertical_subsampling = u32::from(registration.vertical_subsampling);
    let horizontal_grid = u32::from(horizontal_grid_size);
    let vertical_grid = u32::from(vertical_grid_size);
    if horizontal_subsampling == 0
        || vertical_subsampling == 0
        || horizontal_grid == 0
        || vertical_grid == 0
    {
        return Err(invalid_layer());
    }
    let width = registered_extent(
        source_width,
        horizontal_subsampling,
        horizontal_grid,
        registration.horizontal_offset,
    )?;
    let height = registered_extent(
        source_height,
        vertical_subsampling,
        vertical_grid,
        registration.vertical_offset,
    )?;
    let pixels = checked_area(width, height)?;
    Ok((width, height, pixels))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (result, crate::specs::part2_composition_planes(final(colors)@), final(alpha)@)
            == crate::specs::part2_registered_pixel(owned_layer_view(source),
                crate::specs::part2_composition_planes(old(colors)@), old(alpha)@,
                source_position.0, source_position.1,
                destination_position.0, destination_position.1, destination_position.2),
    )
)]
pub(super) fn copy_registered_pixel(
    source: &OwnedLayer,
    source_position: (u32, u32),
    destination_position: (u32, u32, u32),
    colors: &mut [Vec<u16>],
    alpha: &mut [u16],
) -> Result<(), DecodeError> {
    let (source_x, source_y) = source_position;
    let (width, x, y) = destination_position;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = crate::specs::part2_composition_planes(colors@); }
    let source_index = index_of(source.width, source_x, source_y)?;
    let destination = index_of(width, x, y)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_registered_colors_empty(
            initial, owned_layer_view(source).3, source_index, destination);
    }
    let mut color = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant color <= colors.len(), initial.len() == colors.len(),
                initial == crate::specs::part2_composition_planes(old(colors)@),
                alpha@ == old(alpha)@,
                crate::specs::part2_composition_pixel_index(owned_layer_view(source).0,
                    source_position.0, source_position.1) == Some(source_index),
                crate::specs::part2_composition_pixel_index(destination_position.0,
                    destination_position.1, destination_position.2) == Some(destination),
                crate::specs::part2_registered_colors_prefix(
                    initial, owned_layer_view(source).3, source_index, destination, color as nat)
                    == (Ok(()), crate::specs::part2_composition_planes(colors@)),
            decreases colors.len() - color,
        )
    )]
    while color < colors.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_registered_colors_step(
                initial, owned_layer_view(source).3, source_index, destination, color as nat);
        }
        let result = copy_registered_color(source, color, source_index, destination, colors);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = result {
                assert(crate::specs::part2_registered_colors_prefix(
                    initial, owned_layer_view(source).3, source_index, destination, color as nat + 1)
                    == (Err(error), crate::specs::part2_composition_planes(colors@)));
                crate::proofs::production_impl::production_registered_colors_error(
                    initial, owned_layer_view(source).3, source_index, destination, color as nat + 1, initial.len());
                assert(crate::specs::part2_registered_pixel(owned_layer_view(source), initial, old(alpha)@,
                    source_position.0, source_position.1,
                    destination_position.0, destination_position.1, destination_position.2)
                    == (Err(error), crate::specs::part2_composition_planes(colors@), alpha@));
            } else {
                crate::proofs::production_impl::production_mct_unit_result(result);
            }
        }
        result?;
        color = color.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    *alpha.get_mut(destination).ok_or_else(invalid_layer)? = match source.alpha.as_ref() {
        Some(value) => *value.0.get(source_index).ok_or_else(invalid_layer)?,
        None => u16::MAX,
    };
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (result, crate::specs::part2_composition_planes(final(colors)@))
            == crate::specs::part2_registered_color_store(
                crate::specs::part2_composition_planes(old(colors)@), owned_layer_view(source).3,
                color as nat, source_index, destination),
            final(colors)@.len() == old(colors)@.len(),
    )
)]
fn copy_registered_color(
    source: &OwnedLayer,
    color: usize,
    source_index: usize,
    destination: usize,
    colors: &mut [Vec<u16>],
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = colors@; }
    let destination_samples = colors.get_mut(color).ok_or_else(invalid_layer)?;
    let sample = match source.colors.get(color) {
        Some(samples) => samples.get(source_index),
        None => None,
    }
    .ok_or_else(invalid_layer)?;
    *destination_samples
        .get_mut(destination)
        .ok_or_else(invalid_layer)? = *sample;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_composition_planes(colors@) =~=
            crate::specs::part2_composition_planes(before).update(color as int,
                before[color as int]@.update(destination as int, *sample)));
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (result, crate::specs::part2_composition_planes(final(colors)@), final(alpha)@)
            == crate::specs::part2_registered_row(
                (owned_layer_view(source), layer_registration_view(registration), grids, destination.0),
                destination.1, crate::specs::part2_composition_planes(old(colors)@), old(alpha)@),
    )
)]
pub(super) fn copy_registered_row(
    source: &OwnedLayer,
    registration: &jp2::CodestreamRegistration,
    grids: (u16, u16),
    destination: (u32, u32),
    colors: &mut [Vec<u16>],
    alpha: &mut [u16],
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost context = (owned_layer_view(source), layer_registration_view(registration), grids, destination.0);
        let ghost initial_colors = crate::specs::part2_composition_planes(colors@);
        let ghost initial_alpha = alpha@;
    }
    let (width, y) = destination;
    let horizontal_subsampling = u32::from(registration.horizontal_subsampling);
    let vertical_subsampling = u32::from(registration.vertical_subsampling);
    let horizontal_grid = u32::from(grids.0);
    let vertical_grid = u32::from(grids.1);
    if vertical_subsampling == 0 {
        return Err(invalid_layer());
    }
    let source_y_numerator = y
        .checked_mul(vertical_grid)
        .ok_or_else(arithmetic_overflow)?;
    if source_y_numerator >= registration.vertical_offset {
        let source_y = crate::refinement::registered_source_coordinate(
            source_y_numerator,
            registration.vertical_offset,
            vertical_subsampling,
        );
        if source_y < source.height {
            if horizontal_subsampling == 0 {
                return Err(invalid_layer());
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_registered_columns_empty(
                    context, y, source_y, initial_colors, initial_alpha);
                assert(crate::specs::part2_registered_row(context, y, initial_colors, initial_alpha)
                    == crate::specs::part2_registered_columns_prefix(
                        context, y, source_y, initial_colors, initial_alpha, width as nat));
            }
            let mut x = 0_u32;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant x <= width, horizontal_subsampling > 0,
                        context == (owned_layer_view(source), layer_registration_view(registration), grids, destination.0),
                        destination == (width, y),
                        horizontal_subsampling == context.1.1 as u32,
                        horizontal_grid == context.2.0 as u32,
                        initial_colors == crate::specs::part2_composition_planes(old(colors)@),
                        initial_alpha == old(alpha)@,
                        crate::specs::part2_registered_row(context, y, initial_colors, initial_alpha)
                            == crate::specs::part2_registered_columns_prefix(
                                context, y, source_y, initial_colors, initial_alpha, width as nat),
                        crate::specs::part2_registered_columns_prefix(context, y, source_y,
                            initial_colors, initial_alpha, x as nat)
                            == (Ok(()), crate::specs::part2_composition_planes(colors@), alpha@),
                    decreases width - x,
                )
            )]
            while x < width {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_registered_columns_step(
                        context, y, source_y, initial_colors, initial_alpha, x as nat);
                    if (x as nat) * (horizontal_grid as nat) > u32::MAX as nat {
                        crate::proofs::production_impl::production_registered_columns_error(
                            context, y, source_y, initial_colors, initial_alpha, x as nat + 1, width as nat);
                    }
                }
                let source_x_numerator = x
                    .checked_mul(horizontal_grid)
                    .ok_or_else(arithmetic_overflow)?;
                if source_x_numerator >= registration.horizontal_offset {
                    let source_x = crate::refinement::registered_source_coordinate(
                        source_x_numerator,
                        registration.horizontal_offset,
                        horizontal_subsampling,
                    );
                    if source_x < source.width {
                        let result = copy_registered_pixel(
                            source,
                            (source_x, source_y),
                            (width, x, y),
                            colors,
                            alpha,
                        );
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            if let Err(error) = result {
                                assert(crate::specs::part2_registered_columns_prefix(context, y, source_y,
                                    initial_colors, initial_alpha, x as nat + 1)
                                    == (Err(error), crate::specs::part2_composition_planes(colors@), alpha@));
                                crate::proofs::production_impl::production_registered_columns_error(
                                    context, y, source_y, initial_colors, initial_alpha, x as nat + 1, width as nat);
                            } else {
                                crate::proofs::production_impl::production_mct_unit_result(result);
                            }
                        }
                        result?;
                    }
                }
                x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
        }
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures owned_layer_outcome(result) == crate::specs::part2_register_layer(
            owned_layer_view(source), layer_registration_view(registration), horizontal_grid_size, vertical_grid_size),
    )
)]
pub(super) fn register_layer(
    source: &OwnedLayer,
    registration: &jp2::CodestreamRegistration,
    horizontal_grid_size: u16,
    vertical_grid_size: u16,
) -> Result<OwnedLayer, DecodeError> {
    let (width, height, pixels) = registered_layer_geometry(
        source.width,
        source.height,
        registration,
        horizontal_grid_size,
        vertical_grid_size,
    )?;
    let samples = vec![0_u16; pixels];
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost seed = samples; }
    #[cfg(verus_keep_ghost)]
    proof! { assert(seed@ =~= Seq::new(pixels as nat, |_pixel: int| 0u16)); }
    let mut colors = vec![samples; source.colors.len()];
    let mut alpha = vec![0_u16; pixels];
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = owned_layer_view(source);
        let ghost descriptor = layer_registration_view(registration);
        let ghost context = (input, descriptor, (horizontal_grid_size, vertical_grid_size), width);
        let ghost initial_colors = crate::specs::part2_composition_planes(colors@);
        let ghost initial_alpha = alpha@;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|channel: int| 0 <= channel < colors.len() implies
            colors@[channel]@ == seed@ by {
            assert(vstd::pervasive::cloned(seed, colors@[channel]));
            if seed != colors@[channel] {
                assert(vstd::pervasive::strictly_cloned(seed, colors@[channel]));
                assert(colors@[channel]@.len() == seed@.len());
                assert forall|index: int| 0 <= index < pixels implies
                    colors@[channel]@[index] == seed@[index] by {
                    assert(vstd::pervasive::cloned(seed@[index], colors@[channel]@[index]));
                }
                assert(colors@[channel]@ =~= seed@);
            }
        }
        assert forall|channel: int| 0 <= channel < initial_colors.len() implies
            initial_colors[channel] == Seq::new(pixels as nat, |_pixel: int| 0u16) by {
            assert(initial_colors[channel] == colors@[channel]@);
            assert(colors@[channel]@ == seed@);
            assert(seed@ =~= Seq::new(pixels as nat, |_pixel: int| 0u16));
        }
        assert(initial_colors =~= Seq::new(input.3.len(), |_channel: int| Seq::new(pixels as nat, |_pixel: int| 0u16)));
        assert(initial_alpha =~= Seq::new(pixels as nat, |_pixel: int| 0u16));
        crate::proofs::production_impl::production_registered_rows_empty(context, initial_colors, initial_alpha);
    }
    let mut y = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant y <= height,
                input == owned_layer_view(source), descriptor == layer_registration_view(registration),
                context == (input, descriptor, (horizontal_grid_size, vertical_grid_size), width),
                crate::specs::part2_registered_layer_geometry(input.0, input.1, descriptor,
                    horizontal_grid_size, vertical_grid_size) == Ok((width, height, pixels)),
                initial_colors == Seq::new(input.3.len(), |_channel: int| Seq::new(pixels as nat, |_pixel: int| 0u16)),
                initial_alpha == Seq::new(pixels as nat, |_pixel: int| 0u16),
                crate::specs::part2_registered_rows_prefix(context, initial_colors, initial_alpha, y as nat)
                    == (Ok(()), crate::specs::part2_composition_planes(colors@), alpha@),
            decreases height - y,
        )
    )]
    while y < height {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_registered_rows_step(
                context, initial_colors, initial_alpha, y as nat);
        }
        let result = copy_registered_row(
            source,
            registration,
            (horizontal_grid_size, vertical_grid_size),
            (width, y),
            &mut colors,
            &mut alpha,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = result {
                assert(crate::specs::part2_registered_rows_prefix(context, initial_colors, initial_alpha, y as nat + 1)
                    == (Err(error), crate::specs::part2_composition_planes(colors@), alpha@));
                crate::proofs::production_impl::production_registered_rows_error(
                    context, initial_colors, initial_alpha, y as nat + 1, height as nat);
            } else {
                crate::proofs::production_impl::production_mct_unit_result(result);
            }
        }
        result?;
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(OwnedLayer {
        width,
        height,
        color_space: source.color_space,
        colors,
        alpha: Some((
            alpha,
            match source.alpha.as_ref() {
                Some(value) => value.1,
                None => false,
            },
        )),
    })
}
