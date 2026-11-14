//! Fresh upstream geometry owners, separate from final grid and packet storage.
use super::*;
verus! {
pub enum Part2GeometryCapacityContext {
    UniformCounts {size:crate::codestream::ImageSize,style:crate::codestream::CodingStyle,tile:Option<u16>},
    ComponentResolutions {components:u16,styles:crate::codestream::ComponentCodingStyles,discard:u8},
    SelectedResolutions {components:u16,styles:crate::codestream::ComponentCodingStyles,discard:u8},
    DerivedCounts {size:crate::codestream::ImageSize,styles:crate::codestream::ComponentCodingStyles,layers:u16,tile:Option<u16>,discard:u8},
}
pub(crate) open spec fn part2_geometry_capacity_count(context:Part2GeometryCapacityContext)->usize {
    match context {
        Part2GeometryCapacityContext::UniformCounts {size,style,..} =>
            if style.decomposition_levels==u8::MAX || size.components as nat*(style.decomposition_levels as nat+1)>usize::MAX {0usize}
            else {(size.components as nat*(style.decomposition_levels as nat+1)) as usize},
        Part2GeometryCapacityContext::ComponentResolutions {components,..}=>components as usize,
        Part2GeometryCapacityContext::SelectedResolutions {components,..}=>components as usize,
        Part2GeometryCapacityContext::DerivedCounts {size,styles,discard,..} =>
            match part2_component_resolution_counts(size.components,&styles,discard) {
                Err(_)=>0usize,Ok(values)=>if size.components as nat*values.0 as nat>usize::MAX {0usize}
                    else{(size.components as nat*values.0 as nat) as usize},
            },
    }
}
pub(crate) open spec fn part2_geometry_capacity_run(context:Part2GeometryCapacityContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_geometry_capacity_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{
        match events[0] {
            Part2JpipSnapshotEvent::GeometryCapacity {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{
                    Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
                },
            _=>None,
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_geometry_capacity_result(context:Part2GeometryCapacityContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_geometry_capacity_run(context,events),result)
}
pub(crate) proof fn part2_geometry_capacity_observed(context:Part2GeometryCapacityContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_geometry_capacity_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_geometry_capacity_result(context,result),
{
    reveal(part2_geometry_capacity_result);
    let count=part2_geometry_capacity_count(context);
    let calls=if count==0 {Seq::empty()}else{seq![Part2JpipSnapshotEvent::GeometryCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_geometry_capacity_run(context,calls+tail)==Some((result,tail)) by{
        if count==0 {assert(calls+tail =~= tail);}else{assert((calls+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_geometry_capacity_run(context,events),calls,result));
}
pub(crate) open spec fn part2_geometry_descriptors_run(components:u16,styles:&crate::codestream::ComponentCodingStyles,discard:u8,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ComponentResolutionCounts> {
    part2_jpip_snapshot_bind(part2_geometry_capacity_run(Part2GeometryCapacityContext::ComponentResolutions {components,styles:*styles,discard},events),|_:(),rest|
        part2_jpip_snapshot_bind(part2_geometry_capacity_run(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},rest),|_:(),tail|
            Some((part2_component_resolution_counts(components,styles,discard),tail))))
}
#[verifier::opaque]
pub(crate) open spec fn part2_geometry_descriptors_result(components:u16,styles:&crate::codestream::ComponentCodingStyles,discard:u8,
    result:Result<Part2ComponentResolutionCounts,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_geometry_descriptors_run(components,styles,discard,events),result)
}
pub(crate) proof fn part2_geometry_descriptors_second(components:u16,styles:&crate::codestream::ComponentCodingStyles,discard:u8,result:Result<(),crate::DecodeError>)
    requires part2_geometry_capacity_result(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},result),
    ensures part2_cold_framed(|events|part2_jpip_snapshot_bind(part2_geometry_capacity_run(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},events),
        |_:(),rest|Some((part2_component_resolution_counts(components,styles,discard),rest))),
        match result {Err(error)=>Err(error),Ok(())=>part2_component_resolution_counts(components,styles,discard)}),
{
    reveal(part2_geometry_capacity_result);
    let after=part2_component_resolution_counts(components,styles,discard);
    if result.is_ok(){part2_cold_pure(after);}
    part2_cold_bind(|events|part2_geometry_capacity_run(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},events),
        |_:(),rest|Some((after,rest)),result,match result {Err(error)=>Err(error),Ok(())=>after});
}
pub(crate) proof fn part2_geometry_descriptors_normal(components:u16,styles:&crate::codestream::ComponentCodingStyles,discard:u8)
    ensures part2_geometry_descriptors_result(components,styles,discard,part2_component_resolution_counts(components,styles,discard)),
{
    reveal(part2_geometry_capacity_result);reveal(part2_geometry_descriptors_result);
    part2_geometry_capacity_observed(Part2GeometryCapacityContext::ComponentResolutions {components,styles:*styles,discard},Ok(()));
    part2_geometry_capacity_observed(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},Ok(()));
    part2_geometry_descriptors_second(components,styles,discard,Ok(()));
    let result=part2_component_resolution_counts(components,styles,discard);
    let second=|events|part2_jpip_snapshot_bind(part2_geometry_capacity_run(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},events),|_:(),tail|Some((result,tail)));
    part2_decode_eta(second,result);
    part2_cold_bind(|events|part2_geometry_capacity_run(Part2GeometryCapacityContext::ComponentResolutions {components,styles:*styles,discard},events),
        |_:(),rest|second(rest),Ok(()),result);
}
pub(crate) proof fn part2_geometry_descriptors_refused(components:u16,styles:&crate::codestream::ComponentCodingStyles,discard:u8,second:bool)
    requires if second {
        part2_geometry_capacity_result(Part2GeometryCapacityContext::ComponentResolutions {components,styles:*styles,discard},Ok(()))
        &&part2_geometry_capacity_result(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},Err(crate::DecodeError::AllocationFailed))
    }else{part2_geometry_capacity_result(Part2GeometryCapacityContext::ComponentResolutions {components,styles:*styles,discard},Err(crate::DecodeError::AllocationFailed))},
    ensures part2_geometry_descriptors_result(components,styles,discard,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_geometry_capacity_result);reveal(part2_geometry_descriptors_result);
    let tail=|events|part2_jpip_snapshot_bind(part2_geometry_capacity_run(Part2GeometryCapacityContext::SelectedResolutions {components,styles:*styles,discard},events),
        |_:(),rest|Some((part2_component_resolution_counts(components,styles,discard),rest)));
    if second {
        part2_geometry_descriptors_second(components,styles,discard,Err(crate::DecodeError::AllocationFailed));
        part2_decode_eta(tail,Err(crate::DecodeError::AllocationFailed));
    }
    part2_cold_bind(|events|part2_geometry_capacity_run(Part2GeometryCapacityContext::ComponentResolutions {components,styles:*styles,discard},events),
        |_:(),rest|tail(rest),if second{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},Err(crate::DecodeError::AllocationFailed));
}
#[verifier::opaque]
pub(crate) open spec fn part2_geometry_counts_step(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,component:u16,resolution:u8,resolutions:u8,discard:u8,counts:Seq<u32>,total:u64)
    ->Result<(Seq<u32>,u64),crate::DecodeError> {
    if resolution>=resolutions {Ok((counts.push(0),total))}else{
        match part2_resolution_geometry(crate::codestream::selection_geometry_view(size),crate::codestream::image_size_component_count(size),
            crate::codestream::image_size_component_infos(size),crate::decode::resolution_geometry_style(style),component,resolution,tile) {
            Err(error)=>Err(error),
            Ok(geometry)=>match part2_packet_grid_subband_delta(style,resolution) {
                Err(error)=>Err(error),
                Ok(subbands)=>if discard>resolutions {Err(crate::DecodeError::InvalidSelection {reason:crate::SelectionError::ReductionTooLarge})}
                else{match part2_packet_grid_codeblocks(total,geometry.code_blocks,resolution<resolutions-discard,limits) {
                    Err(error)=>Err(error),
                    Ok(next)=>if subbands!=0 && geometry.precincts>u32::MAX {Err(part1_block_placement_error(true))}
                        else{Ok((counts.push(if subbands==0{0u32}else{geometry.precincts as u32}),next))},
                }},
            },
        }
    }
}
pub(crate) proof fn part2_derived_geometry_step(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,
    component:u16,style:crate::codestream::CodingStyle,resolutions:u8,resolution:u8,before:Seq<u32>,total:u64,after:Seq<u32>,next:u64)
    requires component<crate::codestream::image_size_component_count(size),resolution<descriptors.0,
        part2_geometry_counts_step(size,style,limits,tile,component,resolution,resolutions,discard,before,total)==Ok((after,next)),
    ensures forall|events| #[trigger] part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,before,total,events)
        ==part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,after,next,events),
{
    reveal(part2_geometry_counts_step);reveal_with_fuel(part2_grid_resolutions_cold_run,2);reveal_with_fuel(part2_grid_components_cold_run,1);
}
pub(crate) proof fn part2_derived_geometry_component_end(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,
    component:u16,style:crate::codestream::CodingStyle,resolutions:u8,counts:Seq<u32>,total:u64)
    requires component<crate::codestream::image_size_component_count(size),
    ensures forall|events| #[trigger] part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,descriptors.0,counts,total,events)
        ==part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,(component+1) as u16,counts,total,events),
{
    reveal_with_fuel(part2_grid_resolutions_cold_run,2);reveal_with_fuel(part2_grid_components_cold_run,1);
}
pub(crate) proof fn part2_derived_geometry_end(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,
    component:u16,counts:Seq<u32>,total:u64)
    requires component>=crate::codestream::image_size_component_count(size),
    ensures forall|events| #[trigger] part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total,events)
        ==part2_grid_run(layers,crate::codestream::image_size_component_count(size),descriptors.1,counts,if discard==0{None}else{Some(descriptors.2)},limits,events),
{
    reveal_with_fuel(part2_grid_components_cold_run,2);reveal_with_fuel(part2_grid_resolutions_cold_run,1);
}
pub(crate) open spec fn part2_derived_geometry_after_descriptors(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid> {
    if size.components as nat*descriptors.0 as nat>usize::MAX {Some((Err(part1_block_placement_error(true)),events))}
    else {part2_jpip_snapshot_bind(part2_geometry_capacity_run(Part2GeometryCapacityContext::DerivedCounts {size:*size,styles:*styles,layers,tile,discard},events),
        |_:(),rest|part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,0,Seq::empty(),0,rest))}
}
pub(crate) proof fn part2_derived_geometry_after_normal(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts)
    requires part2_component_resolution_counts(size.components,styles,discard)==Ok(descriptors),
    ensures part2_cold_framed(|events|part2_derived_geometry_after_descriptors(size,styles,layers,limits,tile,discard,descriptors,events),
        part2_packet_grid_from_components(size,styles,layers,limits,tile,discard)),
{
    reveal(part2_geometry_capacity_result);
    crate::codestream::selection_geometry_known_fields(size);
    let result=part2_packet_grid_from_components(size,styles,layers,limits,tile,discard);
    if size.components as nat*descriptors.0 as nat>usize::MAX {part2_cold_pure::<Part1PacketGrid>(result);}else{
        let context=Part2GeometryCapacityContext::DerivedCounts {size:*size,styles:*styles,layers,tile,discard};
        part2_geometry_capacity_observed(context,Ok(()));
        part2_grid_components_cold_normal(size,styles,layers,limits,tile,discard,descriptors,0,Seq::empty(),0);
        part2_decode_eta(|events|part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,0,Seq::empty(),0,events),result);
        part2_cold_bind(|events|part2_geometry_capacity_run(context,events),
            |_:(),rest|part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,0,Seq::empty(),0,rest),Ok(()),result);
    }
}
pub(crate) proof fn part2_cold_prefix_result<T>(root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<T>,
    child:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<T>,prefix:Seq<Part2JpipSnapshotEvent>,result:Result<T,crate::DecodeError>)
    requires forall|events|root(prefix+events)==child(events),part2_cold_framed(child,result),
    ensures part2_cold_framed(root,result),
{
    let calls=part2_cold_witness(child,result);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|root((prefix+calls)+tail)==Some((result,tail)) by{
        assert((prefix+calls)+tail =~= prefix+(calls+tail));
        part2_cold_prefix_at(child,calls,result,tail);
    }
    assert(part2_cold_prefix(root,prefix+calls,result));
}
pub(crate) proof fn part2_derived_geometry_prefix(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts)->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires part2_component_resolution_counts(size.components,styles,discard)==Ok(descriptors),
        size.components as nat*descriptors.0 as nat<=usize::MAX,
        part2_geometry_descriptors_result(size.components,styles,discard,Ok(descriptors)),
        part2_geometry_capacity_result(Part2GeometryCapacityContext::DerivedCounts {size:*size,styles:*styles,layers,tile,discard},Ok(())),
    ensures forall|tail| #[trigger] part2_derived_grid_run(size,styles,layers,limits,tile,discard,prefix+tail)
        ==part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,0,Seq::empty(),0,tail),
{
    reveal(part2_geometry_descriptors_result);reveal(part2_geometry_capacity_result);
    reveal(part2_derived_grid_run);crate::codestream::selection_geometry_known_fields(size);
    let first=|events|part2_geometry_descriptors_run(size.components,styles,discard,events);
    let second=|events|part2_geometry_capacity_run(Part2GeometryCapacityContext::DerivedCounts {size:*size,styles:*styles,layers,tile,discard},events);
    let before=part2_cold_witness(first,Ok(descriptors));let after=part2_cold_witness(second,Ok(()));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_derived_grid_run(size,styles,layers,limits,tile,discard,(before+after)+tail)
        ==part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,0,Seq::empty(),0,tail) by{
        assert((before+after)+tail =~= before+(after+tail));
        part2_cold_prefix_at(first,before,Ok(descriptors),after+tail);part2_cold_prefix_at(second,after,Ok(()),tail);
    }
    before+after
}
pub(crate) proof fn part2_derived_geometry_descriptor_error(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,error:crate::DecodeError)
    requires part2_geometry_descriptors_result(size.components,styles,discard,Err(error)),
    ensures part2_derived_grid_result(size,styles,layers,limits,tile,discard,Err(error)),
{
    reveal(part2_derived_grid_result);reveal(part2_geometry_descriptors_result);reveal(part2_derived_grid_run);
    crate::codestream::selection_geometry_known_fields(size);
    part2_cold_bind(|events|part2_geometry_descriptors_run(size.components,styles,discard,events),
        |descriptors:Part2ComponentResolutionCounts,rest|part2_derived_geometry_after_descriptors(size,styles,layers,limits,tile,discard,descriptors,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_derived_geometry_capacity_error(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts)
    requires part2_geometry_descriptors_result(size.components,styles,discard,Ok(descriptors)),
        size.components as nat*descriptors.0 as nat<=usize::MAX,
        part2_geometry_capacity_result(Part2GeometryCapacityContext::DerivedCounts {size:*size,styles:*styles,layers,tile,discard},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_derived_grid_result(size,styles,layers,limits,tile,discard,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_derived_grid_result);reveal(part2_geometry_descriptors_result);reveal(part2_geometry_capacity_result);reveal(part2_derived_grid_run);
    crate::codestream::selection_geometry_known_fields(size);
    part2_cold_bind(|events|part2_geometry_capacity_run(Part2GeometryCapacityContext::DerivedCounts {size:*size,styles:*styles,layers,tile,discard},events),
        |_:(),rest|part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,0,Seq::empty(),0,rest),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
    part2_decode_eta(|events|part2_derived_geometry_after_descriptors(size,styles,layers,limits,tile,discard,descriptors,events),Err(crate::DecodeError::AllocationFailed));
    part2_cold_bind(|events|part2_geometry_descriptors_run(size.components,styles,discard,events),
        |descriptors:Part2ComponentResolutionCounts,rest|part2_derived_geometry_after_descriptors(size,styles,layers,limits,tile,discard,descriptors,rest),Ok(descriptors),Err(crate::DecodeError::AllocationFailed));
}
}
