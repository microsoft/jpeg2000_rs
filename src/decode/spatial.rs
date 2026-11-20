use super::geometry::{component_coordinate_bounds, derive_component_resolution_geometry_for};
use super::{
    CodingStyle, ComponentCodingStyles, DecodeError, ImageSize, PacketGrid, arithmetic_overflow,
    ceil_div_u32,
};
use crate::packet::{PacketSpatialGrid, PacketSpatialResolution};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn packet_spatial_resolution_outcome(result: Result<PacketSpatialResolution, DecodeError>)
        -> Result<crate::specs::Part1PacketSpatialResolution, DecodeError>
    {
        match result { Ok(row)=>Ok(crate::packet::packet_spatial_resolution_view(row)),Err(error)=>Err(error) }
    }
    pub open spec fn spatial_state(rows:Seq<PacketSpatialResolution>,step_x:u64,step_y:u64) -> crate::specs::Part2SpatialGridState {
        crate::specs::Part2SpatialGridState {rows:crate::packet::packet_spatial_rows_view(rows),step_x,step_y}
    }
    pub open spec fn spatial_bounds_outcome(result:Result<[u32;4],DecodeError>) -> Result<Seq<u32>,DecodeError> {
        match result {Err(error)=>Err(error),Ok(bounds)=>Ok(bounds@)}
    }
    pub open spec fn spatial_grid_outcome(result:Result<PacketSpatialGrid,DecodeError>) -> Result<crate::specs::Part1PacketSpatialGrid,DecodeError> {
        match result {Err(error)=>Err(error),Ok(grid)=>Ok(crate::packet::packet_spatial_grid_view(&grid))}
    }
}

#[derive(Clone, Copy)]
pub(crate) enum PacketSpatialStyles<'a> {
    Uniform(CodingStyle),
    Components(&'a ComponentCodingStyles),
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packet_spatial_styles_view(styles: PacketSpatialStyles<'_>)
        -> Seq<Result<CodingStyle, DecodeError>>
    {
        Seq::new(65536, |component:int|match styles {
            PacketSpatialStyles::Uniform(style)=>Ok(style),
            PacketSpatialStyles::Components(styles)=>crate::codestream::component_coding_style_result(styles,component as u16),
        })
    }
    pub(crate) proof fn packet_spatial_styles_known(styles: PacketSpatialStyles<'_>)
        ensures packet_spatial_styles_view(styles)==match styles {
            PacketSpatialStyles::Uniform(style)=>crate::specs::part2_packet_spatial_uniform_styles(style),
            PacketSpatialStyles::Components(styles)=>crate::specs::part2_packet_spatial_component_styles(styles),
        },
    {
        reveal(packet_spatial_styles_view);
        match styles {
            PacketSpatialStyles::Uniform(style)=>{
                assert(packet_spatial_styles_view(styles) =~= crate::specs::part2_packet_spatial_uniform_styles(style));
            },
            PacketSpatialStyles::Components(source)=>{
                assert(packet_spatial_styles_view(styles) =~= crate::specs::part2_packet_spatial_component_styles(source));
            },
        }
    }
}

impl PacketSpatialStyles<'_> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == packet_spatial_styles_view(self)[component as int],
    ))]
    fn style(self, component: u16) -> Result<CodingStyle, DecodeError> {
        match self {
            Self::Uniform(style) => Ok(style),
            Self::Components(styles) => styles.style(component),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_packet_spatial_gcd(left, right),
))]
fn gcd(mut left: u64, mut right: u64) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = (left, right); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_packet_spatial_gcd); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant crate::specs::part2_packet_spatial_gcd(left, right)
            == crate::specs::part2_packet_spatial_gcd(initial.0, initial.1),
        decreases right,
    ))]
    while right != 0 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_packet_spatial_gcd); }
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_packet_spatial_scan_count(start, end, step),
))]
fn scan_count(start: u32, end: u32, step: u64) -> Result<u64, DecodeError> {
    if start >= end {
        return Ok(0);
    }
    if step == 0 {
        return Err(arithmetic_overflow());
    }
    let distance = match (u64::from(end - 1) / step).checked_sub(u64::from(start) / step) {
        Some(value) => value,
        None => return Err(arithmetic_overflow()),
    };
    match distance.checked_add(1) {
        Some(value) => Ok(value),
        None => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_packet_spatial_axis_geometry(start, scale, sampling, exponent, reference_origin),
))]
fn spatial_axis_geometry(
    start: u32,
    scale: u32,
    sampling: u8,
    exponent: u8,
    reference_origin: u32,
) -> Result<(u64, u64, u64), DecodeError> {
    let start = ceil_div_u32(start, scale)?;
    if exponent >= 64 {
        return Err(arithmetic_overflow());
    }
    let width = 1_u64 << u32::from(exponent);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(width != 0) by(bit_vector)
            requires exponent < 64, width == 1u64 << (exponent as u32);
    }
    let sample_step = match u64::from(scale).checked_mul(u64::from(sampling)) {
        Some(value) => value,
        None => return Err(arithmetic_overflow()),
    };
    let step = match sample_step.checked_mul(width) {
        Some(value) => value,
        None => return Err(arithmetic_overflow()),
    };
    let origin = match (u64::from(start) / width).checked_mul(step) {
        Some(value) => value,
        None => return Err(arithmetic_overflow()),
    };
    // B.12.1.3-.5 visit clipped first precincts at the tile origin,
    // but aligned, ceil-rounded resolution origins retain their position.
    let first = if u64::from(start) % width != 0 {
        u64::from(reference_origin)
    } else {
        origin
    };
    Ok((first, origin, step))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_spatial_resolution_outcome(result) == crate::specs::part2_packet_spatial_resolution(
        size, style, component, resolution, tile, reference_origin@),
))]
fn spatial_resolution(
    size: &ImageSize,
    style: CodingStyle,
    component: u16,
    resolution: u8,
    tile: Option<u16>,
    reference_origin: [u32; 2],
) -> Result<PacketSpatialResolution, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::codestream::resolution_selectors_known_fields(style);
        reveal(super::resolution_geometry_style);
    }
    let bounds = component_coordinate_bounds(size, component, tile)?;
    let info = size.component(component)?;
    let (scale_x, scale_y) = style.resolution_downsampling(resolution)?;
    let (exponent_x, exponent_y) = style.precinct_exponents(resolution)?;
    let (first_x, origin_x, step_x) = spatial_axis_geometry(
        bounds[0],
        scale_x,
        info.x_subsampling,
        exponent_x,
        reference_origin[0],
    )?;
    let (first_y, origin_y, step_y) = spatial_axis_geometry(
        bounds[1],
        scale_y,
        info.y_subsampling,
        exponent_y,
        reference_origin[1],
    )?;
    let geometry =
        derive_component_resolution_geometry_for(size, style, component, resolution, tile)?;
    let row = PacketSpatialResolution {
        first_x,
        first_y,
        origin_x,
        origin_y,
        step_x,
        step_y,
        across: geometry.precincts_across,
        down: geometry.precincts_down,
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::packet::packet_spatial_resolution_known_fields(row); }
    Ok(row)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures spatial_bounds_outcome(result) == crate::specs::part2_packet_spatial_bounds(size,tile),
))]
fn reference_bounds(size: &ImageSize, tile: Option<u16>) -> Result<[u32; 4], DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::selection_geometry_known_fields(size); }
    let bounds = match tile {
        Some(index) => {
            let bounds = size.tile_bounds(index)?;
            [bounds.x0, bounds.y0, bounds.x1, bounds.y1]
        }
        None => [
            size.x_origin,
            size.y_origin,
            size.x_origin
                .checked_add(size.width)
                .ok_or_else(arithmetic_overflow)?,
            size.y_origin
                .checked_add(size.height)
                .ok_or_else(arithmetic_overflow)?,
        ],
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_packet_spatial_bounds(size,tile)==Ok(bounds@)) by {
            if let Ok(expected)=crate::specs::part2_packet_spatial_bounds(size,tile) {
                assert(expected =~= bounds@);
            }
        }
    }
    Ok(bounds)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures spatial_grid_outcome(result) == crate::specs::part2_packet_spatial_finish(bounds@,spatial_state(rows@,step_x,step_y)),
))]
fn finish_spatial(
    rows: Vec<PacketSpatialResolution>,
    bounds: [u32; 4],
    step_x: u64,
    step_y: u64,
) -> Result<PacketSpatialGrid, DecodeError> {
    let across = if step_x == 0 {
        0
    } else {
        scan_count(bounds[0], bounds[2], step_x)?
    };
    let down = if step_y == 0 {
        0
    } else {
        scan_count(bounds[1], bounds[3], step_y)?
    };
    let positions = match across.checked_mul(down) {
        Some(value) => value,
        None => return Err(arithmetic_overflow()),
    };
    let grid = PacketSpatialGrid {
        rows,
        x0: bounds[0],
        y0: bounds[1],
        step_x,
        step_y,
        across,
        positions,
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::packet::packet_spatial_grid_known_fields(&grid); }
    Ok(grid)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_packet_spatial_result(crate::packet::packet_grid_view(&grid),size,packet_spatial_styles_view(styles),tile,crate::packet::packet_grid_outcome(result)),
        crate::packet::packet_grid_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        crate::packet::packet_grid_outcome(result)==crate::specs::part2_packet_spatial_value(crate::packet::packet_grid_view(&grid),size,packet_spatial_styles_view(styles),tile),
))]
pub(crate) fn attach_packet_spatial_grid(
    grid: PacketGrid,
    size: &ImageSize,
    styles: PacketSpatialStyles<'_>,
    tile: Option<u16>,
) -> Result<PacketGrid, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source = crate::packet::packet_grid_view(&grid);
        let ghost selectors = packet_spatial_styles_view(styles);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_packet_spatial_normal(source,size,selectors,tile);
        reveal(packet_spatial_styles_view);
    }
    let bounds = reference_bounds(size, tile)?;
    let (components, maximum) = grid.spatial_row_shape();
    let capacity = usize::from(components)
        .checked_mul(usize::from(maximum))
        .ok_or_else(arithmetic_overflow)?;
    let reserved = if capacity == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(capacity)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let context=crate::specs::Part2GridCapacityContext::Spatial {grid:source,size:*size,styles:selectors,tile};
        crate::specs::part2_grid_capacity_observed(context,match reserved {Ok(_)=>Ok(()),Err(error)=>Err(error)});
        if reserved.is_err(){crate::specs::part2_packet_spatial_refused(source,size,selectors,tile);}
    }
    let mut rows = reserved?;
    let mut step_x = 0;
    let mut step_y = 0;
    let mut component = 0_u16;
    #[cfg(verus_keep_ghost)]
    proof! { assert(spatial_state(rows@,step_x,step_y).rows =~= Seq::<crate::specs::Part1PacketSpatialResolution>::empty()); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component <= components, (components,maximum)==(source.components,source.resolutions),
            source==crate::packet::packet_grid_view(&grid),
            rows@.len()==component as nat*maximum as nat,
            selectors==packet_spatial_styles_view(styles),
            selectors.len()==65536,
            capacity as nat==components as nat*maximum as nat,
            crate::specs::part2_packet_spatial_result(source,size,selectors,tile,crate::specs::part2_packet_spatial_value(source,size,selectors,tile)),
            crate::specs::part2_packet_spatial_value(source,size,selectors,tile)
                ==crate::specs::part2_packet_spatial_apply(source,crate::specs::part2_packet_spatial_components(
                    size,selectors,tile,(components,maximum),bounds@,component,spatial_state(rows@,step_x,step_y))),
        decreases components - component,
    ))]
    while component < components {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((component as nat) < selectors.len());
            crate::specs::part2_packet_spatial_component_step(size,selectors,tile,(components,maximum),bounds@,component,spatial_state(rows@,step_x,step_y));
        }
        let style_result = styles.style(component);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(style_result==selectors[component as int]);
            assert(crate::specs::part2_packet_spatial_value(source,size,selectors,tile)
                ==crate::specs::part2_packet_spatial_apply(source,match style_result {
                    Err(error)=>Err(error),
                    Ok(style)=>crate::specs::part2_packet_spatial_resolutions(size,selectors,tile,(components,maximum),bounds@,component,style,0,spatial_state(rows@,step_x,step_y)),
                }));
        }
        let style = match style_result {
            Ok(style) => style,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part2_packet_spatial_value(source,size,selectors,tile)==Err(error));
                }
                return Err(error);
            }
        };
        let mut resolution = 0_u8;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant component < components, resolution <= maximum,
                source==crate::packet::packet_grid_view(&grid),
                (components,maximum)==(source.components,source.resolutions),
                rows@.len()==component as nat*maximum as nat+resolution as nat,
                capacity as nat==components as nat*maximum as nat,
                selectors==packet_spatial_styles_view(styles),
                selectors.len()==65536,
                crate::specs::part2_packet_spatial_result(source,size,selectors,tile,crate::specs::part2_packet_spatial_value(source,size,selectors,tile)),
                crate::specs::part2_packet_spatial_value(source,size,selectors,tile)
                    ==crate::specs::part2_packet_spatial_apply(source,crate::specs::part2_packet_spatial_resolutions(
                        size,selectors,tile,(components,maximum),bounds@,component,style,resolution,spatial_state(rows@,step_x,step_y))),
            decreases maximum - resolution,
        ))]
        while resolution < maximum {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_packet_spatial_resolution_step(size,selectors,tile,(components,maximum),bounds@,component,style,resolution,spatial_state(rows@,step_x,step_y));
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before=spatial_state(rows@,step_x,step_y);}
            let row = if resolution <= style.decomposition_levels {
                let result = spatial_resolution(
                    size,
                    style,
                    component,
                    resolution,
                    tile,
                    [bounds[0], bounds[1]],
                );
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert([bounds[0],bounds[1]]@ =~= seq![bounds[0],bounds[1]]);
                }
                match result {
                    Ok(row) => row,
                    Err(error) => {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(crate::specs::part2_packet_spatial_value(source,size,selectors,tile)==Err(error));
                        }
                        return Err(error);
                    }
                }
            } else {
                PacketSpatialResolution {
                    first_x: 0,
                    first_y: 0,
                    origin_x: 0,
                    origin_y: 0,
                    step_x: 1,
                    step_y: 1,
                    across: 0,
                    down: 0,
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! { crate::packet::packet_spatial_resolution_known_fields(row); }
            if row.across != 0 && row.down != 0 {
                step_x = gcd(gcd(step_x, row.step_x), row.origin_x);
                step_y = gcd(gcd(step_y, row.step_y), row.origin_y);
            }
            rows.push(row);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(spatial_state(rows@,step_x,step_y).rows =~= crate::specs::part2_packet_spatial_push(before,crate::packet::packet_spatial_resolution_view(row)).rows);
                assert(spatial_state(rows@,step_x,step_y) == crate::specs::part2_packet_spatial_push(before,crate::packet::packet_spatial_resolution_view(row)));
            }
            resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(resolution==maximum);
            assert(rows@.len()==(component as nat+1)*maximum as nat) by(nonlinear_arith)
                requires rows@.len()==component as nat*maximum as nat+resolution as nat, resolution==maximum;
            crate::specs::part2_packet_spatial_component_end(size,selectors,tile,(components,maximum),bounds@,component,style,spatial_state(rows@,step_x,step_y));
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal_with_fuel(crate::specs::part2_packet_spatial_components,1);}
    let spatial = finish_spatial(rows, bounds, step_x, step_y)?;
    Ok(grid.with_spatial(spatial))
}
