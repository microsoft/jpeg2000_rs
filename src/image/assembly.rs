use super::arithmetic::{
    arithmetic_overflow, ceil_div, checked_area, index, invalid_image, registered_ceil_div,
};
use super::{
    AssemblyDimensions, AssemblyPlane, AssemblySelection, DecodedComponent, DecodedImage,
    TileComponent,
};
#[cfg(verus_keep_ghost)]
use super::{
    assembly_size_view, assembly_tile_view, assembly_tiles_view, decoded_component_view,
    decoded_components_view, decoded_image_outcome,
};
use crate::codestream::ImageSize;
use crate::decode::PreparedTileComponent;
#[cfg(verus_keep_ghost)]
use crate::decode::{prepared_component_view, prepared_components_view};
use crate::{DecodeError, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_owned_assembly_plane(
        assembly_size_view(size), assembly_tile_view(tile), region, maximum, component, bytes),
))]
fn owned_plane_charge(
    size: &ImageSize,
    tile: TileComponent<'_>,
    region: [u32; 4],
    maximum: u64,
    component: u16,
    bytes: u64,
) -> Option<u64> {
    let dimensions =
        assembly_component_dimensions(size, component, [0, 0], Some((region, 1))).ok()?;
    let count = checked_area(dimensions.1, dimensions.2).ok()?;
    let mut charged = bytes;
    charge_assembly_bytes(count, &mut charged, maximum).ok()?;
    let crop = assembly_component_crop(size, dimensions, true).ok()??;
    if tile.component != component
        || tile.x != 0
        || tile.y != 0
        || tile.width != dimensions.1
        || tile.height != dimensions.2
        || crop != (0, 0, tile.width, tile.height)
        || tile.samples.len() != count
    {
        return None;
    }
    Some(charged)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.is_ok() && result.get_Ok_0() == crate::specs::part2_owned_assembly_eligible(
        assembly_size_view(size), prepared_components_view(prepared@), region, discard, maximum, single_tile),
))]
pub(crate) fn has_owned_full_cover(
    size: &ImageSize,
    prepared: &[PreparedTileComponent],
    region: [u32; 4],
    discard: u8,
    maximum: u64,
    single_tile: bool,
) -> Result<bool, DecodeError> {
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(assembly_size_view); }
    if !single_tile
        || discard != 0
        || prepared.len() != usize::from(size.components)
        || prepared.is_empty()
        || region[0] != size.x_origin
        || region[1] != size.y_origin
        || u64::from(region[2]) != u64::from(size.x_origin) + u64::from(size.width)
        || u64::from(region[3]) != u64::from(size.y_origin) + u64::from(size.height)
        || assembly_selected_header(region, discard).is_err()
    {
        return Ok(false);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost model = assembly_size_view(size);
        let ghost source = prepared_components_view(prepared@);
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_owned_assembly_prefix, 1); }
    let mut bytes = 0;
    let mut component = 0_u16;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component <= size.components, source.len() == size.components,
            model == assembly_size_view(size), source == prepared_components_view(prepared@),
            crate::specs::part2_owned_assembly_prefix(model, source, region, maximum, component as nat) == Some(bytes),
        decreases size.components - component,
    ))]
    while component < size.components {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(usize::from(component))?;
        let tile = prepared[usize::from(component)].as_tile_component();
        let charge = owned_plane_charge(size, tile, region, maximum, component, bytes);
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_owned_assembly_prefix, 1); }
        match charge {
            Some(charged) => bytes = charged,
            None => {
                #[cfg(verus_keep_ghost)]
                proof! { crate::specs::part2_owned_assembly_refusal_persists(model, source, region,
                maximum, component as nat + 1, source.len()); }
                return Ok(false);
            }
        }
        component += 1;
    }
    Ok(true)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::part2_owned_assembly_eligible(assembly_size_view(size),
        prepared_components_view(prepared@), region, 0, _maximum, true),
    ensures crate::specs::part2_owned_assembly_storage_result(assembly_size_view(size),
        prepared_components_view(prepared@), region, _maximum, decoded_image_outcome(result)),
        decoded_image_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            decoded_image_outcome(result) == crate::specs::part1_assemble_selected_image(
                assembly_size_view(size), prepared_components_view(prepared@), region, 0, _maximum),
))]
pub(crate) fn assemble_owned_full_cover(
    size: &ImageSize,
    prepared: Vec<PreparedTileComponent>,
    region: [u32; 4],
    _maximum: u64,
) -> Result<DecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(assembly_size_view); reveal(super::decoded_image_view); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost model = assembly_size_view(size);
        let ghost input = prepared@;
        let ghost source = prepared_components_view(input);
    }
    let (_, x_origin, y_origin, width, height) = assembly_selected_header(region, 0)?;
    let reserved = crate::allocation::empty_with_capacity(prepared.len());
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_owned_assembly_value(model, source, region, _maximum);
        crate::specs::part2_owned_assembly_capacity_observed(model, source, region, _maximum,
            crate::allocation::inspection_capacity_outcome(reserved));
    }
    let mut components = reserved?;
    let mut remaining = prepared.into_iter();
    let mut component = 0_u16;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component <= size.components,
            model == assembly_size_view(size), source == prepared_components_view(input),
            source.len() == size.components,
            crate::specs::part2_owned_assembly_eligible(model, source, region, 0, _maximum, true),
            vstd::std_specs::iter::IteratorSpec::remaining(&remaining) == input.skip(component as int),
            decoded_components_view(components@) == crate::specs::part2_owned_assembly_components(
                model, source, component as nat),
        decreases size.components - component,
    ))]
    while component < size.components {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        let tile = remaining.next().ok_or_else(invalid_image)?;
        let (width, height, fraction_bits) = {
            let source = tile.as_tile_component();
            (source.width, source.height, source.fraction_bits)
        };
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part2_owned_assembly_info(model, source, region, _maximum,
        source.len(), component); }
        let info = crate::codestream::image_component_info(size, component)?;
        let decoded = DecodedComponent {
            width,
            height,
            info,
            fraction_bits,
            samples: tile.into_samples(),
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = components@; }
        components.push(decoded);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(decoded_components_view(components@) =~= decoded_components_view(before).push(
                decoded_component_view(components@[component as int])));
            assert(crate::specs::part2_owned_assembly_components(model, source, component as nat + 1)
                =~= decoded_components_view(components@));
        }
        component += 1;
    }
    Ok(DecodedImage {
        width,
        height,
        x_origin,
        y_origin,
        components,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_assembly_storage_result(crate::specs::Part2AssemblyOwnerContext {
        size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),selection:None,maximum:crate::limits::resource_decoded_bytes_limit(limits)},decoded_image_outcome(result)),
    decoded_image_outcome(result)!=Err(DecodeError::AllocationFailed) ==> decoded_image_outcome(result) == crate::specs::part1_assemble_image(
        assembly_size_view(size), assembly_tiles_view(tiles@), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn assemble_image(
    size: &ImageSize,
    tiles: &[TileComponent<'_>],
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost context=crate::specs::Part2AssemblyOwnerContext {size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),selection:None,maximum:crate::limits::resource_decoded_bytes_limit(limits)};}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_assembly_storage_normal(context);}
    let reserved = if size.components == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(usize::from(size.components))
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let response=crate::allocation::inspection_capacity_outcome(reserved);
        crate::specs::part2_assembly_owner_observed(context,response);
        if reserved.is_err(){crate::specs::part2_assembly_storage_refused(context,response);}
    }
    let components = reserved?;
    let image_x1 = size
        .x_origin
        .checked_add(size.width)
        .ok_or_else(arithmetic_overflow)?;
    let image_y1 = size
        .y_origin
        .checked_add(size.height)
        .ok_or_else(arithmetic_overflow)?;
    let mut image = DecodedImage {
        width: size.width,
        height: size.height,
        x_origin: size.x_origin,
        y_origin: size.y_origin,
        components,
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = image@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_assembly_components_empty(
            original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (image_x1, image_y1),
            None, crate::limits::resource_decoded_bytes_limit(limits),
        );
    }
    let mut decoded_bytes = 0_u64;
    let mut component = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= size.components,
            context==(crate::specs::Part2AssemblyOwnerContext {size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),selection:None,maximum:crate::limits::resource_decoded_bytes_limit(limits)}),
            crate::specs::part2_assembly_storage_result(context,crate::specs::part1_assemble_image(assembly_size_view(size),assembly_tiles_view(tiles@),crate::limits::resource_decoded_bytes_limit(limits))),
            image_x1 as int == size.x_origin as int + size.width as int,
            image_y1 as int == size.y_origin as int + size.height as int,
            original == (size.width, size.height, size.x_origin, size.y_origin, Seq::empty()),
            crate::specs::part1_assembly_components_prefix(
                original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (image_x1, image_y1),
                None, crate::limits::resource_decoded_bytes_limit(limits), component as nat,
            ) == (Ok(()), image@, decoded_bytes),
            decreases size.components - component,
        )
    )]
    while component < size.components {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_assembly_components_step(
                original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (image_x1, image_y1),
                None, crate::limits::resource_decoded_bytes_limit(limits), component as nat,
            );
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=(Ok(()),image@,decoded_bytes);}
        let appended = append_assembly_component(
            &mut image,
            &mut decoded_bytes,
            size,
            tiles,
            component,
            ([image_x1, image_y1], None),
            limits.maximum_decoded_bytes(),
        );
        match appended {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_assembly_storage_plane_error(context,component as nat,before,(appended,image@,decoded_bytes));
                    if error!=DecodeError::AllocationFailed{
                    crate::proofs::production_impl::production_assembly_components_error_persists(
                        original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (image_x1, image_y1),
                        None, crate::limits::resource_decoded_bytes_limit(limits), component as nat + 1, size.components as nat,
                    );
                    }
                }
                return Err(error);
            }
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(image)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_assembly_component_dimensions(
        assembly_size_view(size), component, (extent[0], extent[1]), selection,
    ),
))]
fn assembly_component_dimensions(
    size: &ImageSize,
    component: u16,
    extent: [u32; 2],
    selection: AssemblySelection,
) -> Result<AssemblyDimensions, DecodeError> {
    let info = crate::codestream::image_component_info(size, component)?;
    match selection {
        None => {
            let x1 = registered_ceil_div(
                extent[0],
                u32::from(info.x_subsampling),
                info.x_registration,
            )?;
            let x0 = registered_ceil_div(
                size.x_origin,
                u32::from(info.x_subsampling),
                info.x_registration,
            )?;
            let width = x1.checked_sub(x0).ok_or_else(arithmetic_overflow)?;
            let y1 = registered_ceil_div(
                extent[1],
                u32::from(info.y_subsampling),
                info.y_registration,
            )?;
            let y0 = registered_ceil_div(
                size.y_origin,
                u32::from(info.y_subsampling),
                info.y_registration,
            )?;
            let height = y1.checked_sub(y0).ok_or_else(arithmetic_overflow)?;
            Ok((
                info,
                width,
                height,
                u32::from(info.x_subsampling),
                u32::from(info.y_subsampling),
                x0,
                y0,
            ))
        }
        Some((region, scale)) => {
            let x_divisor = u32::from(info.x_subsampling)
                .checked_mul(scale)
                .ok_or_else(arithmetic_overflow)?;
            let y_divisor = u32::from(info.y_subsampling)
                .checked_mul(scale)
                .ok_or_else(arithmetic_overflow)?;
            let x0 = registered_ceil_div(region[0], x_divisor, info.x_registration)?;
            let y0 = registered_ceil_div(region[1], y_divisor, info.y_registration)?;
            let width = registered_ceil_div(region[2], x_divisor, info.x_registration)?
                .checked_sub(x0)
                .ok_or_else(arithmetic_overflow)?;
            let height = registered_ceil_div(region[3], y_divisor, info.y_registration)?
                .checked_sub(y0)
                .ok_or_else(arithmetic_overflow)?;
            if width == 0 || height == 0 {
                return Err(DecodeError::InvalidSelection {
                    reason: crate::SelectionError::EmptyComponentIntersection,
                });
            }
            Ok((info, width, height, x_divisor, y_divisor, x0, y0))
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_assembly_component_crop(assembly_size_view(size), dimensions, selected),
))]
fn assembly_component_crop(
    size: &ImageSize,
    dimensions: AssemblyDimensions,
    selected: bool,
) -> Result<Option<(u32, u32, u32, u32)>, DecodeError> {
    if !selected {
        return Ok(None);
    }
    let x0 = dimensions
        .5
        .checked_sub(registered_ceil_div(
            size.x_origin,
            dimensions.3,
            dimensions.0.x_registration,
        )?)
        .ok_or_else(arithmetic_overflow)?;
    let y0 = dimensions
        .6
        .checked_sub(registered_ceil_div(
            size.y_origin,
            dimensions.4,
            dimensions.0.y_registration,
        )?)
        .ok_or_else(arithmetic_overflow)?;
    let x1 = x0
        .checked_add(dimensions.1)
        .ok_or_else(arithmetic_overflow)?;
    let y1 = y0
        .checked_add(dimensions.2)
        .ok_or_else(arithmetic_overflow)?;
    Ok(Some((x0, y0, x1, y1)))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(bytes)) == crate::specs::part1_accumulate_decoded_bytes(
        count as nat, *old(bytes), maximum,
    ),
))]
pub(super) fn charge_assembly_bytes(
    count: usize,
    bytes: &mut u64,
    maximum: u64,
) -> Result<(), DecodeError> {
    let component_bytes = (count as u64)
        .checked_mul(8)
        .ok_or_else(arithmetic_overflow)?;
    *bytes = bytes
        .checked_add(component_bytes)
        .ok_or_else(arithmetic_overflow)?;
    if *bytes > maximum {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: maximum,
            actual: *bytes,
        });
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_assembly_plane_result(crate::specs::Part2AssemblyPlaneContext {
        image:old(image)@,bytes:*old(bytes),size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),component,
        extent:(profile.0[0],profile.0[1]),selection:profile.1,maximum},(result,final(image)@,*final(bytes))),
    result!=Err(DecodeError::AllocationFailed) ==> (result, final(image)@, *final(bytes)) == crate::specs::part1_assembly_append_plane(
        old(image)@, *old(bytes), assembly_size_view(size), assembly_tiles_view(tiles@), component,
        (profile.0[0], profile.0[1]), profile.1, maximum,
    ),
))]
pub(super) fn append_assembly_component(
    image: &mut DecodedImage,
    bytes: &mut u64,
    size: &ImageSize,
    tiles: &[TileComponent<'_>],
    component: u16,
    profile: ([u32; 2], AssemblySelection),
    maximum: u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost context=crate::specs::Part2AssemblyPlaneContext {image:image@,bytes:*bytes,size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),component,
    extent:(profile.0[0],profile.0[1]),selection:profile.1,maximum};}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_assembly_plane_normal(context);}
    let (extent, selection) = profile;
    let dimensions = assembly_component_dimensions(size, component, extent, selection)?;
    let count = checked_area(dimensions.1, dimensions.2)?;
    charge_assembly_bytes(count, bytes, maximum)?;
    let crop = assembly_component_crop(size, dimensions, selection.is_some())?;
    let samples_result = crate::allocation::filled_values(0_i64, count);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_assembly_plane_capacity_observed(context,crate::specs::Part2AssemblyPlaneStage::Samples,crate::allocation::inspection_capacity_outcome(samples_result));
        if samples_result.is_err(){crate::specs::part2_assembly_plane_samples_refused(context);}
    }
    let samples = samples_result?;
    let visited_result = crate::allocation::filled_values(false, count);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_assembly_plane_capacity_observed(context,crate::specs::Part2AssemblyPlaneStage::Visited {samples:samples@},crate::allocation::inspection_capacity_outcome(visited_result));
        if visited_result.is_err(){crate::specs::part2_assembly_plane_visited_refused(context);}
    }
    let visited = visited_result?;
    let mut plane = AssemblyPlane {
        width: dimensions.1,
        height: dimensions.2,
        fraction_bits: None,
        samples,
        visited,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(plane.samples@ =~= Seq::new(count as nat, |i: int| 0i64));
        assert(plane.visited@ =~= Seq::new(count as nat, |i: int| false));
    }
    collect_assembly_tiles(&mut plane, tiles, component, crop)?;
    let fraction_bits = plane.fraction_bits.ok_or_else(invalid_image)?;
    let reserved = crate::allocation::reserve_additional(&mut image.components, 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_assembly_plane_capacity_observed(context,crate::specs::Part2AssemblyPlaneStage::Publish {plane:plane@},crate::allocation::inspection_capacity_outcome(reserved));
        if reserved.is_err(){crate::specs::part2_assembly_plane_publish_refused(context,plane@);}
    }
    reserved?;
    image.components.push(DecodedComponent {
        width: dimensions.1,
        height: dimensions.2,
        info: dimensions.0,
        fraction_bits,
        samples: plane.samples,
    });
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(decoded_components_view(image.components@) == decoded_components_view(old(image).components@).push(
            decoded_component_view(image.components@[image.components@.len() - 1]),
        )) by {
            assert forall |i: int| 0 <= i < image.components@.len() implies
                decoded_components_view(image.components@)[i] == decoded_components_view(old(image).components@).push(
                    decoded_component_view(image.components@[image.components@.len() - 1]),
                )[i] by {};
        };
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_assembly_storage_result(crate::specs::Part2AssemblyOwnerContext {
        size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),selection:Some((region,discard_levels)),maximum:crate::limits::resource_decoded_bytes_limit(limits)},decoded_image_outcome(result)),
    decoded_image_outcome(result)!=Err(DecodeError::AllocationFailed) ==> decoded_image_outcome(result) == crate::specs::part1_assemble_selected_image(
        assembly_size_view(size), assembly_tiles_view(tiles@), region, discard_levels,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(crate) fn assemble_selected_image(
    size: &ImageSize,
    tiles: &[TileComponent<'_>],
    region: [u32; 4],
    discard_levels: u8,
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost context=crate::specs::Part2AssemblyOwnerContext {size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),selection:Some((region,discard_levels)),maximum:crate::limits::resource_decoded_bytes_limit(limits)};}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_assembly_storage_normal(context);}
    let header = assembly_selected_header(region, discard_levels)?;
    let reserved = if size.components == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(usize::from(size.components))
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let response=crate::allocation::inspection_capacity_outcome(reserved);
        crate::specs::part2_assembly_owner_observed(context,response);
        if reserved.is_err(){crate::specs::part2_assembly_storage_refused(context,response);}
    }
    let components = reserved?;
    let mut image = DecodedImage {
        width: header.3,
        height: header.4,
        x_origin: header.1,
        y_origin: header.2,
        components,
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = image@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_assembly_components_empty(
            original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (0, 0),
            Some((region, header.0)), crate::limits::resource_decoded_bytes_limit(limits),
        );
    }
    let mut decoded_bytes = 0_u64;
    let mut component = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= size.components,
            context==(crate::specs::Part2AssemblyOwnerContext {size:assembly_size_view(size),tiles:assembly_tiles_view(tiles@),selection:Some((region,discard_levels)),maximum:crate::limits::resource_decoded_bytes_limit(limits)}),
            crate::specs::part2_assembly_storage_result(context,crate::specs::part1_assemble_selected_image(assembly_size_view(size),assembly_tiles_view(tiles@),region,discard_levels,crate::limits::resource_decoded_bytes_limit(limits))),
            crate::specs::part1_assembly_selected_header(region, discard_levels) == Ok(header),
            original == (header.3, header.4, header.1, header.2, Seq::empty()),
            crate::specs::part1_assembly_components_prefix(
                original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (0, 0),
                Some((region, header.0)), crate::limits::resource_decoded_bytes_limit(limits), component as nat,
            ) == (Ok(()), image@, decoded_bytes),
            decreases size.components - component,
        )
    )]
    while component < size.components {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_assembly_components_step(
                original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (0, 0),
                Some((region, header.0)), crate::limits::resource_decoded_bytes_limit(limits), component as nat,
            );
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=(Ok(()),image@,decoded_bytes);}
        let appended = append_assembly_component(
            &mut image,
            &mut decoded_bytes,
            size,
            tiles,
            component,
            ([0, 0], Some((region, header.0))),
            limits.maximum_decoded_bytes(),
        );
        match appended {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_assembly_storage_plane_error(context,component as nat,before,(appended,image@,decoded_bytes));
                    if error!=DecodeError::AllocationFailed{
                    crate::proofs::production_impl::production_assembly_components_error_persists(
                        original, 0, assembly_size_view(size), assembly_tiles_view(tiles@), (0, 0),
                        Some((region, header.0)), crate::limits::resource_decoded_bytes_limit(limits),
                        component as nat + 1, size.components as nat,
                    );
                    }
                }
                return Err(error);
            }
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(image)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_assembly_selected_header(region, discard_levels),
))]
fn assembly_selected_header(
    region: [u32; 4],
    discard_levels: u8,
) -> Result<(u32, u32, u32, u32, u32), DecodeError> {
    if region[0] >= region[2] || region[1] >= region[3] || discard_levels > 31 {
        return Err(invalid_image());
    }
    let scale = 1_u32 << u32::from(discard_levels);
    let x0 = ceil_div(region[0], scale)?;
    let y0 = ceil_div(region[1], scale)?;
    let width = ceil_div(region[2], scale)?
        .checked_sub(x0)
        .ok_or_else(arithmetic_overflow)?;
    let height = ceil_div(region[3], scale)?
        .checked_sub(y0)
        .ok_or_else(arithmetic_overflow)?;
    if width == 0 || height == 0 {
        return Err(invalid_image());
    }
    Ok((scale, x0, y0, width, height))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(plane)@) == crate::specs::part1_assembly_pixel(
        old(plane)@, assembly_tile_view(tile), position[0], position[1], crop,
    ),
))]
fn assembly_pixel(
    plane: &mut AssemblyPlane,
    tile: TileComponent<'_>,
    position: [u32; 2],
    crop: Option<(u32, u32)>,
) -> Result<(), DecodeError> {
    let destination_x = match crop {
        None => tile
            .x
            .checked_add(position[0])
            .ok_or_else(arithmetic_overflow)?,
        Some(origin) => position[0]
            .checked_sub(origin.0)
            .ok_or_else(arithmetic_overflow)?,
    };
    let destination_y = match crop {
        None => tile
            .y
            .checked_add(position[1])
            .ok_or_else(arithmetic_overflow)?,
        Some(origin) => position[1]
            .checked_sub(origin.1)
            .ok_or_else(arithmetic_overflow)?,
    };
    let destination = index(plane.width, destination_x, destination_y)?;
    let source_x = match crop {
        None => position[0],
        Some(_) => position[0]
            .checked_sub(tile.x)
            .ok_or_else(arithmetic_overflow)?,
    };
    let source_y = match crop {
        None => position[1],
        Some(_) => position[1]
            .checked_sub(tile.y)
            .ok_or_else(arithmetic_overflow)?,
    };
    let source = index(tile.width, source_x, source_y)?;
    if destination >= plane.samples.len()
        || destination >= plane.visited.len()
        || source >= tile.samples.len()
        || plane.visited[destination]
    {
        return Err(invalid_image());
    }
    plane.samples[destination] = tile.samples[source];
    plane.visited[destination] = true;
    Ok(())
}

#[cfg(verus_keep_ghost)]
verus! {
    proof fn assembly_row_bulk_equivalence(
        original: crate::specs::Part1AssemblyPlane,
        tile: crate::specs::Part1AssemblyTile,
        x_start: u32,
        y: u32,
        crop: Option<(u32, u32)>,
        dst_start: usize,
        src_start: usize,
        count: usize,
        k: nat,
    )
        requires
            k <= count,
            x_start as nat + count <= u32::MAX,
            dst_start + count <= original.3.len(),
            dst_start + count <= original.4.len(),
            src_start + count <= tile.6.len(),
            match crop {
                Some(origin) =>
                    x_start >= origin.0 && y >= origin.1
                    && x_start >= tile.1 && y >= tile.2
                    && crate::specs::part1_transform_offset((y - origin.1) as u32, original.0, (x_start - origin.0) as u32) == Ok(dst_start)
                    && crate::specs::part1_transform_offset((y - tile.2) as u32, tile.3, (x_start - tile.1) as u32) == Ok(src_start),
                None =>
                    (tile.1 as nat) + (x_start as nat) + count <= u32::MAX + 1
                    && (tile.2 as nat) + (y as nat) <= u32::MAX
                    && crate::specs::part1_transform_offset((tile.2 + y) as u32, original.0, (tile.1 + x_start) as u32) == Ok(dst_start)
                    && crate::specs::part1_transform_offset(y, tile.3, x_start) == Ok(src_start),
            },
            forall |j: int| 0 <= j < count ==> !#[trigger] original.4[dst_start as int + j],
        ensures ({
            let res = crate::specs::part1_assembly_row_prefix(original, tile, x_start, y, crop, k);
            res.0 == Ok::<(), DecodeError>(())
                && res.1.0 == original.0
                && res.1.1 == original.1
                && res.1.2 == original.2
                && res.1.3 =~= Seq::new(original.3.len(), |i: int|
                    if dst_start <= i < dst_start + k { tile.6[src_start as int + (i - dst_start as int)] } else { original.3[i] })
                && res.1.4 =~= Seq::new(original.4.len(), |i: int|
                    if dst_start <= i < dst_start + k { true } else { original.4[i] })
        }),
        decreases k,
    {
        if k == 0 {
            let res = crate::specs::part1_assembly_row_prefix(original, tile, x_start, y, crop, 0);
            assert(res.1.3 =~= original.3);
            assert(res.1.4 =~= original.4);
        } else {
            let prev_k = (k - 1) as nat;
            assembly_row_bulk_equivalence(original, tile, x_start, y, crop, dst_start, src_start, count, prev_k);
            let prev = crate::specs::part1_assembly_row_prefix(original, tile, x_start, y, crop, prev_k);
            let x_cur = (x_start as nat + prev_k) as u32;
            match crop {
                Some(origin) => {
                    assert(crate::specs::part1_transform_offset((y - origin.1) as u32, original.0, (x_cur - origin.0) as u32)
                        == Ok((dst_start + prev_k) as usize));
                    assert(crate::specs::part1_transform_offset((y - tile.2) as u32, tile.3, (x_cur - tile.1) as u32)
                        == Ok((src_start + prev_k) as usize));
                }
                None => {
                    assert(crate::specs::part1_transform_offset((tile.2 + y) as u32, original.0, (tile.1 + x_cur) as u32)
                        == Ok((dst_start + prev_k) as usize));
                    assert(crate::specs::part1_transform_offset(y, tile.3, x_cur)
                        == Ok((src_start + prev_k) as usize));
                }
            }
            assert(!prev.1.4[dst_start as int + prev_k as int]);
            let res = crate::specs::part1_assembly_row_prefix(original, tile, x_start, y, crop, k);
            assert(res.0 == Ok::<(), DecodeError>(()));
            assert(res.1.3 =~= Seq::new(original.3.len(), |i: int|
                if dst_start <= i < dst_start + k { tile.6[src_start as int + (i - dst_start as int)] } else { original.3[i] }));
            assert(res.1.4 =~= Seq::new(original.4.len(), |i: int|
                if dst_start <= i < dst_start + k { true } else { original.4[i] }));
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires start + count <= visited.len(),
    ensures result == forall |j: int| 0 <= j < count ==> !#[trigger] visited@[start as int + j],
))]
#[inline]
fn visited_span_clear(visited: &[bool], start: usize, count: usize) -> bool {
    let span = &visited[start..start + count];
    let mut i = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= count, span.len() == count,
            forall |j: int| 0 <= j < i ==> !#[trigger] span@[j],
        decreases count - i,
    ))]
    while i < count {
        if span[i] {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(plane)@) == crate::specs::part1_assembly_row_prefix(
        old(plane)@, assembly_tile_view(tile), row[0], row[2], crop,
        if row[0] >= row[1] { 0nat } else { (row[1] - row[0]) as nat },
    ),
))]
fn assembly_row(
    plane: &mut AssemblyPlane,
    tile: TileComponent<'_>,
    row: [u32; 3],
    crop: Option<(u32, u32)>,
) -> Result<(), DecodeError> {
    if row[0] >= row[1] {
        return Ok(());
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = plane@; }
    let count_u32 = row[1] - row[0];
    if let Ok(count) = usize::try_from(count_u32) {
        let fast_offsets = match crop {
            None => {
                if let (Some(dx0), Some(dy)) =
                    (tile.x.checked_add(row[0]), tile.y.checked_add(row[2]))
                {
                    if dx0.checked_add(count_u32 - 1).is_some() {
                        match (
                            index(plane.width, dx0, dy),
                            index(tile.width, row[0], row[2]),
                        ) {
                            (Ok(dst), Ok(src)) => Some((dst, src)),
                            _ => None,
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Some(origin) => {
                if row[0] >= origin.0 && row[2] >= origin.1 && row[0] >= tile.x && row[2] >= tile.y
                {
                    match (
                        index(plane.width, row[0] - origin.0, row[2] - origin.1),
                        index(tile.width, row[0] - tile.x, row[2] - tile.y),
                    ) {
                        (Ok(dst), Ok(src)) => Some((dst, src)),
                        _ => None,
                    }
                } else {
                    None
                }
            }
        };
        #[allow(
            clippy::collapsible_if,
            reason = "MSRV 1.88 and Verus require separate if-let bindings."
        )]
        if let Some((dst_start, src_start)) = fast_offsets {
            if dst_start <= plane.samples.len()
                && count <= plane.samples.len() - dst_start
                && dst_start <= plane.visited.len()
                && count <= plane.visited.len() - dst_start
                && src_start <= tile.samples.len()
                && count <= tile.samples.len() - src_start
                && visited_span_clear(&plane.visited, dst_start, count)
            {
                let dst_s = &mut plane.samples.as_mut_slice()[dst_start..dst_start + count];
                let src_s = &tile.samples[src_start..src_start + count];
                let mut i = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant i <= count,
                        dst_s.len() == count, src_s.len() == count,
                        forall |j: int| 0 <= j < i ==> #[trigger] dst_s@[j] == src_s@[j],
                    decreases count - i,
                ))]
                while i < count {
                    dst_s[i] = src_s[i];
                    i += 1;
                }
                let dst_v = &mut plane.visited.as_mut_slice()[dst_start..dst_start + count];
                let mut j = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant j <= count,
                        dst_v.len() == count,
                        forall |k: int| 0 <= k < j ==> #[trigger] dst_v@[k],
                    decreases count - j,
                ))]
                while j < count {
                    dst_v[j] = true;
                    j += 1;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assembly_row_bulk_equivalence(
                        original, assembly_tile_view(tile), row[0], row[2], crop,
                        dst_start, src_start, count, count as nat,
                    );
                    let expected = crate::specs::part1_assembly_row_prefix(
                        original, assembly_tile_view(tile), row[0], row[2], crop, count as nat,
                    );
                    assert(plane.samples@ =~= expected.1.3);
                    assert(plane.visited@ =~= expected.1.4);
                }
                return Ok(());
            }
        }
    }
    let mut x = row[0];
    let mut passes = row[1].checked_sub(row[0]).ok_or_else(arithmetic_overflow)?;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row[0] <= x <= row[1],
        passes == row[1] - x,
        original == old(plane)@,
        crate::specs::part1_assembly_row_prefix(
            original, assembly_tile_view(tile), row[0], row[2], crop, (x - row[0]) as nat,
        ) == (Ok(()), plane@),
        decreases passes,
    ))]
    while x < row[1] {
        match assembly_pixel(plane, tile, [x, row[2]], crop) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_assembly_row_error_persists(
                        original, assembly_tile_view(tile), row[0], row[2], crop,
                        (x - row[0]) as nat + 1, (row[1] - row[0]) as nat,
                    );
                }
                return Err(error);
            }
        }
        x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        passes = passes.checked_sub(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(plane)@) == crate::specs::part1_assembly_rectangle(
        old(plane)@, assembly_tile_view(tile), (rectangle[0], rectangle[1], rectangle[2], rectangle[3]), crop,
    ),
))]
fn assembly_rectangle(
    plane: &mut AssemblyPlane,
    tile: TileComponent<'_>,
    rectangle: [u32; 4],
    crop: Option<(u32, u32)>,
) -> Result<(), DecodeError> {
    if rectangle[0] >= rectangle[2] || rectangle[1] >= rectangle[3] {
        return Ok(());
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = plane@; }
    let mut y = rectangle[1];
    let mut passes = rectangle[3]
        .checked_sub(rectangle[1])
        .ok_or_else(arithmetic_overflow)?;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant rectangle[0] < rectangle[2],
        rectangle[1] <= y <= rectangle[3],
        passes == rectangle[3] - y,
        original == old(plane)@,
        crate::specs::part1_assembly_rectangle_prefix(
            original, assembly_tile_view(tile), (rectangle[0], rectangle[1], rectangle[2], rectangle[3]),
            crop, (y - rectangle[1]) as nat,
        ) == (Ok(()), plane@),
        decreases passes,
    ))]
    while y < rectangle[3] {
        match assembly_row(plane, tile, [rectangle[0], rectangle[2], y], crop) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_assembly_rectangle_error_persists(
                        original, assembly_tile_view(tile), (rectangle[0], rectangle[1], rectangle[2], rectangle[3]), crop,
                        (y - rectangle[1]) as nat + 1, (rectangle[3] - rectangle[1]) as nat,
                    );
                }
                return Err(error);
            }
        }
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
        passes = passes.checked_sub(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(plane)@) == crate::specs::part1_place_assembly_tile(old(plane)@, assembly_tile_view(tile)),
))]
fn place_tile(plane: &mut AssemblyPlane, tile: TileComponent<'_>) -> Result<(), DecodeError> {
    if tile.width == 0
        || tile.height == 0
        || tile
            .x
            .checked_add(tile.width)
            .ok_or_else(arithmetic_overflow)?
            > plane.width
        || tile
            .y
            .checked_add(tile.height)
            .ok_or_else(arithmetic_overflow)?
            > plane.height
        || tile.samples.len() != checked_area(tile.width, tile.height)?
    {
        return Err(invalid_image());
    }
    assembly_rectangle(plane, tile, [0, 0, tile.width, tile.height], None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(plane)@) == crate::specs::part1_place_selected_tile(
        old(plane)@, assembly_tile_view(tile), (crop[0], crop[1], crop[2], crop[3]),
    ),
))]
fn place_selected_tile(
    plane: &mut AssemblyPlane,
    tile: TileComponent<'_>,
    crop: [u32; 4],
) -> Result<(), DecodeError> {
    let x0 = tile.x.max(crop[0]);
    let y0 = tile.y.max(crop[1]);
    let x1 = tile
        .x
        .checked_add(tile.width)
        .ok_or_else(arithmetic_overflow)?
        .min(crop[2]);
    let y1 = tile
        .y
        .checked_add(tile.height)
        .ok_or_else(arithmetic_overflow)?
        .min(crop[3]);
    assembly_rectangle(plane, tile, [x0, y0, x1, y1], Some((crop[0], crop[1])))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(plane)@) == crate::specs::part1_assembly_tile_step(
        old(plane)@, assembly_tile_view(tile), component, crop,
    ),
))]
fn assembly_tile_step(
    plane: &mut AssemblyPlane,
    tile: TileComponent<'_>,
    component: u16,
    crop: Option<(u32, u32, u32, u32)>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_assembly_tile_step); }
    if tile.component != component {
        return Ok(());
    }
    if plane.fraction_bits.is_some() && plane.fraction_bits != Some(tile.fraction_bits) {
        return Err(invalid_image());
    }
    plane.fraction_bits = Some(tile.fraction_bits);
    match crop {
        None => place_tile(plane, tile),
        Some(region) => place_selected_tile(plane, tile, [region.0, region.1, region.2, region.3]),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (forall |i: int| 0 <= i < visited.len() ==> visited[i]),
))]
fn all_pixels_visited(visited: &[bool]) -> bool {
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= visited.len(),
        forall |i: int| 0 <= i < index ==> visited[i],
        decreases visited.len() - index,
    ))]
    while index < visited.len() {
        if !visited[index] {
            return false;
        }
        index += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(plane)@) == crate::specs::part1_collect_assembly_tiles(
        old(plane)@, assembly_tiles_view(tiles@), component, crop,
    ),
    result.is_ok() ==> final(plane).fraction_bits.is_some(),
))]
fn collect_assembly_tiles(
    plane: &mut AssemblyPlane,
    tiles: &[TileComponent<'_>],
    component: u16,
    crop: Option<(u32, u32, u32, u32)>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = plane@; }
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_assembly_tiles_empty(
            original, assembly_tiles_view(tiles@), component, crop,
        );
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= tiles.len(),
        original == old(plane)@,
        crate::specs::part1_assembly_tiles_prefix(
            original, assembly_tiles_view(tiles@), component, crop, index as nat,
        ) == (Ok(()), plane@),
        decreases tiles.len() - index,
    ))]
    while index < tiles.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = plane@; }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(assembly_tiles_view(tiles@)[index as int] == assembly_tile_view(tiles[index as int]));
            crate::proofs::production_impl::production_assembly_tiles_step(
                original, assembly_tiles_view(tiles@), component, crop, index as nat,
            );
            assert(crate::specs::part1_assembly_tiles_prefix(
                original, assembly_tiles_view(tiles@), component, crop, index as nat + 1,
            ) == crate::specs::part1_assembly_tile_step(
                before, assembly_tile_view(tiles[index as int]), component, crop,
            ));
        }
        let tile = tiles[index];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(assembly_tile_view(tile) == assembly_tile_view(tiles[index as int]));
        }
        let transition = assembly_tile_step(plane, tile, component, crop);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((transition, plane@) == crate::specs::part1_assembly_tile_step(
                before, assembly_tile_view(tile), component, crop,
            ));
            assert(assembly_tile_view(tile) == assembly_tile_view(tiles[index as int]));
        }
        match transition {
            Ok(()) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(transition.is_ok());
                    assert(transition->Ok_0 == ());
                    assert(transition == Ok(()));
                    assert((transition, plane@) == crate::specs::part1_assembly_tile_step(
                        before, assembly_tile_view(tile), component, crop,
                    ));
                    assert((Ok(()), plane@) == crate::specs::part1_assembly_tile_step(
                        before, assembly_tile_view(tiles[index as int]), component, crop,
                    ));
                }
            }
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_assembly_tiles_error_persists(
                        original, assembly_tiles_view(tiles@), component, crop, index as nat + 1, tiles.len() as nat,
                    );
                }
                return Err(error);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_assembly_tiles_prefix(
                original, assembly_tiles_view(tiles@), component, crop, index as nat + 1,
            ) == (Ok(()), plane@));
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part1_assembly_tiles_prefix(
            original, assembly_tiles_view(tiles@), component, crop, tiles.len() as nat,
        ) == (Ok(()), plane@));
        assert(assembly_tiles_view(tiles@).len() == tiles.len());
    }
    if plane.fraction_bits.is_none() || !all_pixels_visited(&plane.visited) {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(plane.fraction_bits.is_none() || !(forall |i: int|
                0 <= i < plane.visited@.len() ==> plane.visited@[i]));
            assert(plane@.2 == plane.fraction_bits);
            assert(plane@.4 == plane.visited@);
            assert(crate::specs::part1_assembly_tiles_prefix(
                original, assembly_tiles_view(tiles@), component, crop, assembly_tiles_view(tiles@).len(),
            ) == (Ok(()), plane@));
            assert(crate::specs::part1_collect_assembly_tiles(
                original, assembly_tiles_view(tiles@), component, crop,
            ) == (Err(crate::specs::part1_assembly_coverage_error(crop.is_some())), plane@));
        }
        return Err(if crop.is_some() {
            DecodeError::InvalidSelection {
                reason: crate::SelectionError::RegionOutsideSelectedTiles,
            }
        } else {
            invalid_image()
        });
    }
    Ok(())
}
