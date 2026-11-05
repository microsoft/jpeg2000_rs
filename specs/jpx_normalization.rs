//! General-layer component registration, including exact traversal error order.

use super::*;

verus! {

pub struct Part2PlaneRegistration {
    pub source: Seq<u16>,
    pub source_width: u32,
    pub source_height: u32,
    pub width: u32,
    pub height: u32,
    pub horizontal_subsampling: u32,
    pub vertical_subsampling: u32,
    pub horizontal_grid: u32,
    pub vertical_grid: u32,
    pub horizontal_offset: u32,
    pub vertical_offset: u32,
}

pub(crate) proof fn part2_plane_index_bound(width: u32, height: u32, x: u32, y: u32, area: usize)
    requires x < width, y < height, part2_layer_area(width, height) == Ok(area),
    ensures part2_composition_pixel_index(width, x, y)
        == Some((y as nat * width as nat + x as nat) as usize),
        (y as nat * width as nat + x as nat) < area as nat,
{
    reveal(part2_layer_area);
    reveal(part2_composition_pixel_index);
    reveal(part2_row_major_index);
    let w = width as int;
    let h = height as int;
    let column = x as int;
    let row = y as int;
    assert(row * w + column < w * h) by(nonlinear_arith)
        requires 0 <= column < w, 0 <= row < h;
    assert(width as nat * height as nat == area as nat);
}

#[verifier::opaque]
pub open spec fn part2_plane_registration_columns(
    context: Part2PlaneRegistration, y: u32, source_y: u32, initial: Seq<u16>, count: nat,
) -> Result<Seq<u16>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) }
    else {
        match part2_plane_registration_columns(context, y, source_y, initial, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(output) => {
                let x = (count - 1) as u32;
                let numerator = x as nat * context.horizontal_grid as nat;
                if numerator > u32::MAX as nat { Err(part2_composition_error(true)) }
                else if numerator < context.horizontal_offset as nat { Ok(output) }
                else {
                    let source_x = ((numerator - context.horizontal_offset as nat) as nat) / context.horizontal_subsampling as nat;
                    if source_x >= context.source_width as nat { Ok(output) }
                    else { Ok(output.update((y as nat * context.width as nat + x as nat) as int,
                        context.source[(source_y as nat * context.source_width as nat + source_x) as int])) }
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_plane_registration_rows(
    context: Part2PlaneRegistration, initial: Seq<u16>, count: nat,
) -> Result<Seq<u16>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) }
    else {
        match part2_plane_registration_rows(context, initial, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(output) => {
                let y = (count - 1) as u32;
                let numerator = y as nat * context.vertical_grid as nat;
                if numerator > u32::MAX as nat { Err(part2_composition_error(true)) }
                else if numerator < context.vertical_offset as nat { Ok(output) }
                else {
                    let source_y = ((numerator - context.vertical_offset as nat) as nat) / context.vertical_subsampling as nat;
                    if source_y >= context.source_height as nat { Ok(output) }
                    else { part2_plane_registration_columns(context, y, source_y as u32, output, context.width as nat) }
                }
            },
        }
    }
}

pub open spec fn part2_register_component_plane(context: Part2PlaneRegistration) -> Result<Seq<u16>, crate::DecodeError> {
    match part2_layer_area(context.source_width, context.source_height) {
        Err(error) => Err(error),
        Ok(source_area) => {
            if context.source.len() != source_area as nat || context.horizontal_subsampling == 0
                || context.vertical_subsampling == 0 || context.horizontal_grid == 0 || context.vertical_grid == 0
            { Err(part2_composition_error(false)) }
            else {
                match part2_layer_area(context.width, context.height) {
                    Err(error) => Err(error),
                    Ok(area) => part2_plane_registration_rows(context, Seq::new(area as nat, |_index: int| 0u16), context.height as nat),
                }
            }
        },
    }
}

pub(crate) proof fn part2_plane_columns_step(
    context: Part2PlaneRegistration, y: u32, source_y: u32, initial: Seq<u16>, count: nat,
)
    ensures part2_plane_registration_columns(context, y, source_y, initial, count + 1)
        == match part2_plane_registration_columns(context, y, source_y, initial, count) {
            Err(error) => Err(error),
            Ok(output) => {
                let x = count as u32;
                let numerator = x as nat * context.horizontal_grid as nat;
                if numerator > u32::MAX as nat { Err(part2_composition_error(true)) }
                else if numerator < context.horizontal_offset as nat { Ok(output) }
                else {
                    let source_x = ((numerator - context.horizontal_offset as nat) as nat) / context.horizontal_subsampling as nat;
                    if source_x >= context.source_width as nat { Ok(output) }
                    else { Ok(output.update((y as nat * context.width as nat + x as nat) as int,
                        context.source[(source_y as nat * context.source_width as nat + source_x) as int])) }
                }
            },
        },
{
    reveal(part2_plane_registration_columns);
}

pub(crate) proof fn part2_plane_columns_error(
    context: Part2PlaneRegistration, y: u32, source_y: u32, initial: Seq<u16>,
    prefix: nat, count: nat, error: crate::DecodeError,
)
    requires prefix <= count, part2_plane_registration_columns(context, y, source_y, initial, prefix) == Err(error),
    ensures part2_plane_registration_columns(context, y, source_y, initial, count) == Err(error),
    decreases count - prefix,
{
    if count > prefix {
        part2_plane_columns_error(context, y, source_y, initial, prefix, (count - 1) as nat, error);
        reveal(part2_plane_registration_columns);
    }
}

pub(crate) proof fn part2_plane_rows_step(context: Part2PlaneRegistration, initial: Seq<u16>, count: nat)
    ensures part2_plane_registration_rows(context, initial, count + 1)
        == match part2_plane_registration_rows(context, initial, count) {
            Err(error) => Err(error),
            Ok(output) => {
                let y = count as u32;
                let numerator = y as nat * context.vertical_grid as nat;
                if numerator > u32::MAX as nat { Err(part2_composition_error(true)) }
                else if numerator < context.vertical_offset as nat { Ok(output) }
                else {
                    let source_y = ((numerator - context.vertical_offset as nat) as nat) / context.vertical_subsampling as nat;
                    if source_y >= context.source_height as nat { Ok(output) }
                    else { part2_plane_registration_columns(context, y, source_y as u32, output, context.width as nat) }
                }
            },
        },
{
    reveal(part2_plane_registration_rows);
}

pub(crate) proof fn part2_plane_rows_error(
    context: Part2PlaneRegistration, initial: Seq<u16>, prefix: nat, count: nat, error: crate::DecodeError,
)
    requires prefix <= count, part2_plane_registration_rows(context, initial, prefix) == Err(error),
    ensures part2_plane_registration_rows(context, initial, count) == Err(error),
    decreases count - prefix,
{
    if count > prefix {
        part2_plane_rows_error(context, initial, prefix, (count - 1) as nat, error);
        reveal(part2_plane_registration_rows);
    }
}

}
