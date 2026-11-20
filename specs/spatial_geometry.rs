use super::*;
use vstd::prelude::*;

verus! {
pub open spec fn part2_packet_spatial_uniform_styles(style:crate::codestream::CodingStyle) -> Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>> {
    Seq::new(65536,|_:int|Ok(style))
}
pub open spec fn part2_packet_spatial_component_styles(styles:&crate::codestream::ComponentCodingStyles) -> Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>> {
    Seq::new(65536,|component:int|crate::codestream::component_coding_style_result(styles,component as u16))
}

#[verifier::opaque]
pub open spec fn part2_packet_spatial_gcd(left: u64, right: u64) -> u64
    decreases right,
{
    if right == 0 { left } else { part2_packet_spatial_gcd(right, (left % right) as u64) }
}

pub open spec fn part2_packet_spatial_bounds(size:&crate::codestream::ImageSize,tile:Option<u16>) -> Result<Seq<u32>,crate::DecodeError> {
    let geometry=crate::codestream::selection_geometry_view(size);
    match tile {
        Some(index)=>match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size),index) {
            Err(error)=>Err(error),Ok(bounds)=>Ok(seq![bounds.x0,bounds.y0,bounds.x1,bounds.y1]),
        },
        None=>if geometry.2 as nat+geometry.0 as nat>u32::MAX || geometry.3 as nat+geometry.1 as nat>u32::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        }else{Ok(seq![geometry.2,geometry.3,(geometry.2+geometry.0) as u32,(geometry.3+geometry.1) as u32])},
    }
}

pub struct Part2SpatialGridState {
    pub rows:Seq<Part1PacketSpatialResolution>,
    pub step_x:u64,
    pub step_y:u64,
}

pub open spec fn part2_packet_spatial_empty() -> Part1PacketSpatialResolution {
    Part1PacketSpatialResolution { first_x:0,first_y:0,origin_x:0,origin_y:0,step_x:1,step_y:1,across:0,down:0 }
}

pub open spec fn part2_packet_spatial_push(state:Part2SpatialGridState,row:Part1PacketSpatialResolution)->Part2SpatialGridState {
    let active=row.across!=0 && row.down!=0;
    Part2SpatialGridState {
        rows:state.rows.push(row),
        step_x:if active {part2_packet_spatial_gcd(part2_packet_spatial_gcd(state.step_x,row.step_x),row.origin_x)}else{state.step_x},
        step_y:if active {part2_packet_spatial_gcd(part2_packet_spatial_gcd(state.step_y,row.step_y),row.origin_y)}else{state.step_y},
    }
}

pub open spec fn part2_packet_spatial_finish(bounds:Seq<u32>,state:Part2SpatialGridState) -> Result<Part1PacketSpatialGrid,crate::DecodeError> {
    let across=if state.step_x==0{Ok(0u64)}else{part2_packet_spatial_scan_count(bounds[0],bounds[2],state.step_x)};
    match across {
        Err(error)=>Err(error),Ok(across)=>{
            let down=if state.step_y==0{Ok(0u64)}else{part2_packet_spatial_scan_count(bounds[1],bounds[3],state.step_y)};
            match down {
                Err(error)=>Err(error),Ok(down)=>if across as nat*down as nat>u64::MAX {
                    Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                }else{Ok(Part1PacketSpatialGrid {
                    rows:state.rows,x0:bounds[0],y0:bounds[1],step_x:state.step_x,step_y:state.step_y,across,
                    positions:(across*down) as u64,
                })},
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_packet_spatial_components(
    size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,
    tile:Option<u16>,shape:(u16,u8),bounds:Seq<u32>,component:u16,state:Part2SpatialGridState,
) -> Result<Part1PacketSpatialGrid,crate::DecodeError>
    decreases if component<shape.0{(shape.0-component) as nat}else{0nat},1nat,0nat,
{
    if component>=shape.0 {part2_packet_spatial_finish(bounds,state)}
    else if component as nat>=styles.len(){Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))}
    else{match styles[component as int] {
        Err(error)=>Err(error),Ok(style)=>part2_packet_spatial_resolutions(size,styles,tile,shape,bounds,component,style,0,state),
    }}
}

#[verifier::opaque]
pub open spec fn part2_packet_spatial_resolutions(
    size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,
    tile:Option<u16>,shape:(u16,u8),bounds:Seq<u32>,component:u16,style:crate::codestream::CodingStyle,resolution:u8,state:Part2SpatialGridState,
) -> Result<Part1PacketSpatialGrid,crate::DecodeError>
    decreases if component<shape.0{(shape.0-component) as nat}else{0nat},0nat,if resolution<shape.1{(shape.1-resolution) as nat}else{0nat},
{
    if component>=shape.0{Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))}
    else if resolution>=shape.1 {part2_packet_spatial_components(size,styles,tile,shape,bounds,(component+1) as u16,state)}
    else{
        let row=if resolution<=style.decomposition_levels {
            part2_packet_spatial_resolution(size,style,component,resolution,tile,seq![bounds[0],bounds[1]])
        }else{Ok(part2_packet_spatial_empty())};
        match row {
            Err(error)=>Err(error),
            Ok(row)=>part2_packet_spatial_resolutions(size,styles,tile,shape,bounds,component,style,(resolution+1) as u8,part2_packet_spatial_push(state,row)),
        }
    }
}

pub proof fn part2_packet_spatial_component_step(
    size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,
    tile:Option<u16>,shape:(u16,u8),bounds:Seq<u32>,component:u16,state:Part2SpatialGridState,
)
    requires component<shape.0,(component as nat) < styles.len(),
    ensures part2_packet_spatial_components(size,styles,tile,shape,bounds,component,state)
        ==match styles[component as int] {
            Err(error)=>Err(error),
            Ok(style)=>part2_packet_spatial_resolutions(size,styles,tile,shape,bounds,component,style,0,state),
        },
{
    reveal_with_fuel(part2_packet_spatial_components,2);
    reveal_with_fuel(part2_packet_spatial_resolutions,1);
}

pub proof fn part2_packet_spatial_resolution_step(
    size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,
    tile:Option<u16>,shape:(u16,u8),bounds:Seq<u32>,component:u16,style:crate::codestream::CodingStyle,resolution:u8,state:Part2SpatialGridState,
)
    requires component<shape.0,resolution<shape.1,
    ensures part2_packet_spatial_resolutions(size,styles,tile,shape,bounds,component,style,resolution,state)
        ==match if resolution<=style.decomposition_levels {
            part2_packet_spatial_resolution(size,style,component,resolution,tile,seq![bounds[0],bounds[1]])
        }else{Ok(part2_packet_spatial_empty())} {
            Err(error)=>Err(error),
            Ok(row)=>part2_packet_spatial_resolutions(size,styles,tile,shape,bounds,component,style,(resolution+1) as u8,part2_packet_spatial_push(state,row)),
        },
{
    reveal_with_fuel(part2_packet_spatial_resolutions,2);
    reveal_with_fuel(part2_packet_spatial_components,1);
}

pub proof fn part2_packet_spatial_component_end(
    size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,
    tile:Option<u16>,shape:(u16,u8),bounds:Seq<u32>,component:u16,style:crate::codestream::CodingStyle,state:Part2SpatialGridState,
)
    requires component<shape.0,
    ensures part2_packet_spatial_resolutions(size,styles,tile,shape,bounds,component,style,shape.1,state)
        ==part2_packet_spatial_components(size,styles,tile,shape,bounds,(component+1) as u16,state),
{
    reveal_with_fuel(part2_packet_spatial_resolutions,2);
    reveal_with_fuel(part2_packet_spatial_components,1);
}

pub open spec fn part2_packet_spatial_value(
    grid:Part1PacketGrid,size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,tile:Option<u16>,
) -> Result<Part1PacketGrid,crate::DecodeError> {
    match part2_packet_spatial_bounds(size,tile) {
        Err(error)=>Err(error),
        Ok(bounds)=>if grid.components as nat*grid.resolutions as nat>usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
        else{match part2_packet_spatial_components(size,styles,tile,(grid.components,grid.resolutions),bounds,0,
            Part2SpatialGridState {rows:Seq::empty(),step_x:0,step_y:0}) {
            Err(error)=>Err(error),Ok(spatial)=>Ok(Part1PacketGrid {spatial:Some(spatial),..grid}),
        }},
    }
}

pub open spec fn part2_packet_spatial_apply(grid:Part1PacketGrid,spatial:Result<Part1PacketSpatialGrid,crate::DecodeError>) -> Result<Part1PacketGrid,crate::DecodeError> {
    match spatial {Err(error)=>Err(error),Ok(spatial)=>Ok(Part1PacketGrid {spatial:Some(spatial),..grid})}
}

pub(crate) open spec fn part2_packet_spatial_run(
    grid:Part1PacketGrid,size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,tile:Option<u16>,
    events:Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1PacketGrid> {
    match part2_packet_spatial_bounds(size,tile) {
        Err(error)=>Some((Err(error),events)),
        Ok(_)=>if grid.components as nat*grid.resolutions as nat>usize::MAX {
            Some((Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),events))
        }else{
            part2_jpip_snapshot_bind(part2_grid_capacity_run(Part2GridCapacityContext::Spatial {grid,size:*size,styles,tile},events),
                |_:(),rest|Some((part2_packet_spatial_value(grid,size,styles,tile),rest)))
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_packet_spatial_result(
    grid:Part1PacketGrid,size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,tile:Option<u16>,
    result:Result<Part1PacketGrid,crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events|part2_packet_spatial_run(grid,size,styles,tile,events),result)
}

pub(crate) proof fn part2_packet_spatial_normal(
    grid:Part1PacketGrid,size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,tile:Option<u16>,
)
    ensures part2_packet_spatial_result(grid,size,styles,tile,part2_packet_spatial_value(grid,size,styles,tile)),
{
    reveal(part2_packet_spatial_result);reveal(part2_grid_capacity_result);
    let result=part2_packet_spatial_value(grid,size,styles,tile);
    match part2_packet_spatial_bounds(size,tile) {
        Err(_)=>{part2_cold_pure::<Part1PacketGrid>(result);},
        Ok(_)=>if grid.components as nat*grid.resolutions as nat>usize::MAX {part2_cold_pure::<Part1PacketGrid>(result);}
        else{
            let context=Part2GridCapacityContext::Spatial {grid,size:*size,styles,tile};
            part2_grid_capacity_observed(context,Ok(()));part2_cold_pure(result);
            part2_cold_bind(|events|part2_grid_capacity_run(context,events),
                |_:(),rest|Some((result,rest)),Ok(()),result);
        },
    }
}

pub(crate) proof fn part2_packet_spatial_refused(
    grid:Part1PacketGrid,size:&crate::codestream::ImageSize,styles:Seq<Result<crate::codestream::CodingStyle,crate::DecodeError>>,tile:Option<u16>,
)
    requires part2_packet_spatial_bounds(size,tile).is_ok(),grid.components as nat*grid.resolutions as nat<=usize::MAX,
        part2_grid_capacity_result(Part2GridCapacityContext::Spatial {grid,size:*size,styles,tile},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_packet_spatial_result(grid,size,styles,tile,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_packet_spatial_result);reveal(part2_grid_capacity_result);
    let context=Part2GridCapacityContext::Spatial {grid,size:*size,styles,tile};
    part2_cold_bind(|events|part2_grid_capacity_run(context,events),
        |_:(),rest|Some((part2_packet_spatial_value(grid,size,styles,tile),rest)),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}

pub open spec fn part2_packet_spatial_scan_count(start: u32, end: u32, step: u64) -> Result<u64, crate::DecodeError> {
    if start >= end { Ok(0) }
    else if step == 0 { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else {
        let last = (end as int - 1) / step as int;
        let first = start as int / step as int;
        if last < first || last - first + 1 > u64::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else { Ok((last - first + 1) as u64) }
    }

}

    pub open spec fn part2_packet_spatial_axis_geometry(
        start:u32,scale:u32,sampling:u8,exponent:u8,reference_origin:u32,
    ) -> Result<(u64,u64,u64),crate::DecodeError> {
        match part2_selection_ceil(start,scale) {
            Err(error)=>Err(error),
            Ok(start)=>if exponent>=64 {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else{
                let width=1u64 << (exponent as u32);
                let sample_step=scale as nat*sampling as nat;
                let step=sample_step*width as nat;
                let base=(start as nat / width as nat)*step;
                let origin=base;
                if sample_step>u64::MAX || step>u64::MAX || base>u64::MAX {
                    Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                }else{
                    Ok((if start as nat % width as nat !=0 {reference_origin as u64}else{origin as u64},origin as u64,step as u64))
                }
            },
        }
    }

    pub open spec fn part2_packet_spatial_resolution(
        size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
        component:u16,resolution:u8,tile:Option<u16>,reference_origin:Seq<u32>,
    ) -> Result<Part1PacketSpatialResolution,crate::DecodeError> {
        let geometry_style=crate::decode::resolution_geometry_style(style);
        match part2_component_coordinate_bounds(crate::codestream::selection_geometry_view(size),
            crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),component,tile) {
            Err(error)=>Err(error),
            Ok(bounds)=>match part1_image_size_component(crate::codestream::image_size_component_count(size),
                crate::codestream::image_size_component_infos(size),component) {
                Err(error)=>Err(error),
                Ok(info)=>match part2_resolution_downsampling(geometry_style.0,geometry_style.1,resolution) {
                    Err(error)=>Err(error),
                    Ok(scales)=>match part2_precinct_exponents(geometry_style.0,geometry_style.4,resolution) {
                        Err(error)=>Err(error),
                        Ok(exponents)=>match part2_packet_spatial_axis_geometry(bounds[0],scales.0,info.x_subsampling,exponents.0,reference_origin[0]) {
                            Err(error)=>Err(error),
                            Ok(x)=>match part2_packet_spatial_axis_geometry(bounds[1],scales.1,info.y_subsampling,exponents.1,reference_origin[1]) {
                                Err(error)=>Err(error),
                                Ok(y)=>match part2_resolution_geometry(crate::codestream::selection_geometry_view(size),
                                    crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
                                    geometry_style,component,resolution,tile) {
                                    Err(error)=>Err(error),
                                    Ok(geometry)=>Ok(Part1PacketSpatialResolution {
                                        first_x:x.0,origin_x:x.1,step_x:x.2,first_y:y.0,origin_y:y.1,step_y:y.2,
                                        across:geometry.precincts_across,down:geometry.precincts_down,
                                    }),
                                },
                            },
                        },
                    },
                },
            },
        }
}
}
