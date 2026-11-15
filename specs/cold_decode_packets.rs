//! Packet preparation capacity composition through actual source-derived decode plans.
use super::*;
verus! {

pub(crate) proof fn part2_decode_eta<T>(run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>, result: Result<T,crate::DecodeError>)
    requires part2_cold_framed(run,result),
    ensures forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<T>|
        (forall|events| #[trigger] other(events)==run(events)) ==> #[trigger] part2_cold_framed(other,result),
{
    part2_cold_framed_extensional(run,run,result);
}
pub(crate) open spec fn part2_packet_value_run(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<(crate::packet::TilePacketDecode, Seq<Part1PacketPrecinctState>)> {
    match part2_packet_run(parts, grid, precincts, selection, limits, events) {
        None => None, Some(((Err(error), _), rest)) => Some((Err(error), rest)),
        Some(((Ok(value), after), rest)) => Some((Ok((value, after)), rest)),
    }
}
    pub(crate) open spec fn part2_layout_decode_run(input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>,
        limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1DecodedImageModel> {
        let initial = Part2DecodedLayoutTile { prepared: Seq::empty(), counters: (0, 0, 0), mct_work: 0 };
        match part2_decoder_execution_admission(input) {
            Err(error) => Some((Err(error), events)),
            Ok(()) => match requested {
                None => match part2_selection_tile_count(crate::codestream::selection_geometry_view(&input.size)) {
                    Err(error) => Some((Err(error), events)),
                    Ok(count) => if count > u16::MAX as u64 + 1 {
                        Some((Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidImageGeometry }), events))
                    } else { part2_full_decode_run(&input.size, input.parts, input.capabilities, limits, count, 0, initial, events) },
                },
                Some(selection) => match part2_validate_selection(crate::codestream::selection_geometry_view(&input.size), selection) {
                    Err(error) => Some((Err(error), events)),
                    Ok(selection) => if selection.1.len() != 4 { Some((Err(part1_block_placement_error(false)), events)) }
                        else { part2_selected_decode_run(&input.size, input.parts, input.capabilities, selection.0,
                            [selection.1[0], selection.1[1], selection.1[2], selection.1[3]], selection.2, limits, 0, initial, events) },
                },
            },
        }
    }
    #[verifier::opaque]
    pub(crate) open spec fn part2_layout_decode_result(input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>,
        limits: &crate::ResourceLimits, result: Result<Part1DecodedImageModel, crate::DecodeError>) -> bool {
        part2_cold_framed(|events| part2_layout_decode_run(input, requested, limits, events), result)
    }
    pub(crate) proof fn part2_layout_decode_normal(input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>, limits: &crate::ResourceLimits)
        ensures part2_layout_decode_result(input, requested, limits, match requested {
            None => part2_decode_layout_input(input, limits), Some(selection) => part2_decode_layout_selected_value_input(input, selection, limits),
        }),
    {
        reveal(part2_layout_decode_result);
        let result = match requested { None => part2_decode_layout_input(input, limits), Some(selection) => part2_decode_layout_selected_value_input(input, selection, limits) };
        let initial = Part2DecodedLayoutTile { prepared: Seq::empty(), counters: (0, 0, 0), mct_work: 0 };
        match part2_decoder_execution_admission(input) {
            Err(_) => { part2_cold_pure::<Part1DecodedImageModel>(result); },
            Ok(()) => match requested {
                None => match part2_selection_tile_count(crate::codestream::selection_geometry_view(&input.size)) {
                    Err(_) => { part2_cold_pure::<Part1DecodedImageModel>(result); },
                    Ok(count) => if count > u16::MAX as u64 + 1 { part2_cold_pure::<Part1DecodedImageModel>(result); }
                        else {
                            part2_full_decode_normal(&input.size, input.parts, input.capabilities, limits, count, 0, initial);
                            part2_decode_eta(|events|part2_full_decode_run(&input.size,input.parts,input.capabilities,limits,count,0,initial,events),
                                part2_full_layout_tiles(&input.size,input.parts,input.capabilities,limits,count,0,initial));
                        },
                },
                Some(selection) => match part2_validate_selection(crate::codestream::selection_geometry_view(&input.size), selection) {
                    Err(_) => { part2_cold_pure::<Part1DecodedImageModel>(result); },
                    Ok(selection) => if selection.1.len() != 4 { part2_cold_pure::<Part1DecodedImageModel>(result); }
                        else { part2_selected_decode_normal(&input.size, input.parts, input.capabilities, selection.0,
                            [selection.1[0], selection.1[1], selection.1[2], selection.1[3]], selection.2, limits, 0, initial);
                            part2_decode_eta(|events|part2_selected_decode_run(&input.size,input.parts,input.capabilities,selection.0,
                                [selection.1[0],selection.1[1],selection.1[2],selection.1[3]],selection.2,limits,0,initial,events),
                                part2_selected_layout_tiles(&input.size,input.parts,input.capabilities,selection.0,
                                [selection.1[0],selection.1[1],selection.1[2],selection.1[3]],selection.2,limits,0,initial));
                    },
                },
            },
        }
    }
    pub(crate) proof fn part2_decode_prefix_error<A, B>(root: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<B>,
        child: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<A>,
        next: spec_fn(A, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<B>, prefix: Seq<Part2JpipSnapshotEvent>, error: crate::DecodeError)
        requires forall|tail| root(prefix + tail) == part2_jpip_snapshot_bind(child(tail), next),
            part2_cold_framed(child, Err(error)),
        ensures part2_cold_framed(root, Err(error)),
    {
        let calls = part2_cold_witness(child, Err(error));
        assert forall|tail: Seq<Part2JpipSnapshotEvent>| root((prefix + calls) + tail) == Some((Err(error), tail)) by {
            assert((prefix + calls) + tail =~= prefix + (calls + tail));
            part2_cold_prefix_at(child, calls, Err(error), tail);
        }
        assert(part2_cold_prefix(root, prefix + calls, Err(error)));
    }
    pub(crate) proof fn part2_decode_prefix_advance<A, B>(root: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<B>,
        child: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<A>,
        next: spec_fn(A, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<B>, prefix: Seq<Part2JpipSnapshotEvent>, after: A)
        -> (extended: Seq<Part2JpipSnapshotEvent>)
        requires forall|tail| root(prefix + tail) == part2_jpip_snapshot_bind(child(tail), next),
            part2_cold_framed(child, Ok(after)),
        ensures forall|tail| root(extended + tail) == next(after, tail),
    {
        let calls = part2_cold_witness(child, Ok(after));
        assert forall|tail: Seq<Part2JpipSnapshotEvent>| root((prefix + calls) + tail) == next(after, tail) by {
            assert((prefix + calls) + tail =~= prefix + (calls + tail));
            part2_cold_prefix_at(child, calls, Ok(after), tail);
        }
        prefix + calls
    }
pub(crate) proof fn part2_packet_value_actual(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    result: (Result<crate::packet::TilePacketDecode, crate::DecodeError>, Seq<Part1PacketPrecinctState>))
    requires part2_packet_result(parts, grid, precincts, selection, limits, result),
    ensures part2_cold_framed(|events| part2_packet_value_run(parts, grid, precincts, selection, limits, events),
        match result.0 { Err(error) => Err(error), Ok(value) => Ok((value, result.1)) }),
{
    reveal(part2_packet_result);
    let prefix = choose|prefix: Seq<Part2JpipSnapshotEvent>| part2_packet_prefix(parts, grid, precincts, selection, limits, prefix, result);
    assert forall|tail: Seq<Part2JpipSnapshotEvent>| part2_packet_value_run(parts, grid, precincts, selection, limits, prefix + tail)
        == Some((match result.0 { Err(error) => Err(error), Ok(value) => Ok((value, result.1)) }, tail)) by {};
    assert(part2_cold_prefix(|events| part2_packet_value_run(parts, grid, precincts, selection, limits, events), prefix,
        match result.0 { Err(error) => Err(error), Ok(value) => Ok((value, result.1)) }));
}
pub(crate) open spec fn part2_planned_decode_run(plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>,
    first: Part2OwnedTilePart, size: &crate::codestream::ImageSize, standard: (bool, bool), selection: Option<Seq<u8>>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2DecodedTileComponents> {
    part2_jpip_snapshot_bind(part2_packet_value_run(parts, plan.grid, plan.precincts, selection, limits, events),
        |decoded: (crate::packet::TilePacketDecode, Seq<Part1PacketPrecinctState>), rest|
            part2_planned_extraction_run(plan,first,size,standard,limits,prepared,work,decoded.1,rest))
}
pub(crate) open spec fn part2_planned_extraction_run(plan:Part2ProgressionTilePlan,first:Part2OwnedTilePart,size:&crate::codestream::ImageSize,standard:(bool,bool),
    limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,work:u64,precincts:Seq<Part1PacketPrecinctState>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2DecodedTileComponents> {
    part2_jpip_snapshot_bind(part2_extraction_tile_calls_run(prepared,plan.components,part2_precinct_decoder_planes(precincts),first.component_coding_styles,
        part2_owned_kernel_registry(first.part2_extensions),crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),first.multiple_component_transform,
        standard,work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),events),
        |effect:Part2ExtractionTileEffect,rest|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(Part2DecodedTileComponents {prepared:effect.1,mct_work:effect.2})},rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_planned_decode_result(plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>,
    first: Part2OwnedTilePart, size: &crate::codestream::ImageSize, standard: (bool, bool), selection: Option<Seq<u8>>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, result: Result<Part2DecodedTileComponents, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_planned_decode_run(plan, parts, first, size, standard, selection, limits, prepared, work, events), result)
}
pub(crate) proof fn part2_planned_decode_normal(plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>,
    first: Part2OwnedTilePart, size: &crate::codestream::ImageSize, standard: (bool, bool), selection: Option<Seq<u8>>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64)
    ensures part2_planned_decode_result(plan, parts, first, size, standard, selection, limits, prepared, work,
        part2_decode_planned_tile_components_owned(plan, parts, first, size, standard, selection, limits, prepared, work)),
{
    reveal(part2_planned_decode_result);
    part2_packet_normal(parts, plan.grid, plan.precincts, selection, limits);
    let execution = part1_progression_tile_decode_owned(parts, plan.grid, plan.precincts, selection, limits);
    part2_packet_value_actual(parts, plan.grid, plan.precincts, selection, limits, execution);
    let result = part2_decode_planned_tile_components_owned(plan, parts, first, size, standard, selection, limits, prepared, work);
    if let Ok(value)=execution.0 {
        part2_planned_extraction_normal(plan,first,size,standard,limits,prepared,work,execution.1);
        part2_decode_eta(|events|part2_planned_extraction_run(plan,first,size,standard,limits,prepared,work,execution.1,events),result);
    }
    part2_cold_bind(|events| part2_packet_value_run(parts, plan.grid, plan.precincts, selection, limits, events),
        |decoded: (crate::packet::TilePacketDecode, Seq<Part1PacketPrecinctState>), rest| part2_planned_extraction_run(plan,first,size,standard,limits,prepared,work,decoded.1,rest),
        match execution.0 { Err(error) => Err(error), Ok(value) => Ok((value, execution.1)) }, result);
}
pub(crate) proof fn part2_planned_decode_packet_error(plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>,
    first: Part2OwnedTilePart, size: &crate::codestream::ImageSize, standard: (bool, bool), selection: Option<Seq<u8>>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, error: crate::DecodeError, after: Seq<Part1PacketPrecinctState>)
    requires part2_packet_result(parts, plan.grid, plan.precincts, selection, limits, (Err(error), after)),
    ensures part2_planned_decode_result(plan, parts, first, size, standard, selection, limits, prepared, work, Err(error)),
{
    reveal(part2_planned_decode_result);
    part2_packet_value_actual(parts, plan.grid, plan.precincts, selection, limits, (Err(error), after));
    part2_cold_bind(|events| part2_packet_value_run(parts, plan.grid, plan.precincts, selection, limits, events),
        |decoded: (crate::packet::TilePacketDecode, Seq<Part1PacketPrecinctState>), rest|
            part2_planned_extraction_run(plan,first,size,standard,limits,prepared,work,decoded.1,rest), Err(error), Err(error));
}
pub(crate) proof fn part2_planned_extraction_normal(plan:Part2ProgressionTilePlan,first:Part2OwnedTilePart,size:&crate::codestream::ImageSize,standard:(bool,bool),
    limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,work:u64,precincts:Seq<Part1PacketPrecinctState>)
    ensures part2_cold_framed(|events|part2_planned_extraction_run(plan,first,size,standard,limits,prepared,work,precincts,events),
        match part2_reconstruct_planned_tile(prepared,plan.components,part2_precinct_decoder_planes(precincts),first.component_coding_styles,
            part2_owned_kernel_registry(first.part2_extensions),crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
            first.multiple_component_transform,standard,work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits)){
                (Err(error),_,_)=>Err(error),(Ok(()),tiles,after_work)=>Ok(Part2DecodedTileComponents {prepared:tiles,mct_work:after_work}),
        }),
{
    let planes=part2_precinct_decoder_planes(precincts);let kernels=part2_owned_kernel_registry(first.part2_extensions);
    let effect=part2_reconstruct_planned_tile(prepared,plan.components,planes,first.component_coding_styles,kernels,
        crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),first.multiple_component_transform,standard,work,
        crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));
    let result=match effect.0{Err(error)=>Err(error),Ok(())=>Ok(Part2DecodedTileComponents {prepared:effect.1,mct_work:effect.2})};
    part2_extraction_tile_normal(prepared,plan.components,planes,first.component_coding_styles,kernels,crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
        first.multiple_component_transform,standard,work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));
    part2_extraction_tile_calls_observed(prepared,plan.components,planes,first.component_coding_styles,kernels,crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
        first.multiple_component_transform,standard,work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),effect);
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_extraction_tile_calls_run(prepared,plan.components,planes,first.component_coding_styles,kernels,crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
        first.multiple_component_transform,standard,work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),events),
        |effect:Part2ExtractionTileEffect,rest|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(Part2DecodedTileComponents {prepared:effect.1,mct_work:effect.2})},rest)),Ok(effect),result);
}
pub(crate) proof fn part2_planned_extraction_error(plan:Part2ProgressionTilePlan,parts:Seq<Part2OwnedTilePart>,first:Part2OwnedTilePart,size:&crate::codestream::ImageSize,standard:(bool,bool),
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,prepared:Seq<Part1AssemblyTile>,work:u64,decoded:crate::packet::TilePacketDecode,precincts:Seq<Part1PacketPrecinctState>,after:Seq<Part1AssemblyTile>,after_work:u64,error:crate::DecodeError)
    requires part2_packet_result(parts,plan.grid,plan.precincts,selection,limits,(Ok(decoded),precincts)),
        part2_extraction_tile_result(prepared,plan.components,part2_precinct_decoder_planes(precincts),first.component_coding_styles,part2_owned_kernel_registry(first.part2_extensions),
            crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),first.multiple_component_transform,standard,work,
            crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),(Err(error),after,after_work)),
    ensures part2_planned_decode_result(plan,parts,first,size,standard,selection,limits,prepared,work,Err(error)),
{
    reveal(part2_planned_decode_result);
    let effect=(Err(error),after,after_work);let planes=part2_precinct_decoder_planes(precincts);let kernels=part2_owned_kernel_registry(first.part2_extensions);
    part2_packet_value_actual(parts,plan.grid,plan.precincts,selection,limits,(Ok(decoded),precincts));
    part2_extraction_tile_calls_observed(prepared,plan.components,planes,first.component_coding_styles,kernels,crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
        first.multiple_component_transform,standard,work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),effect);
    part2_cold_pure(Err::<Part2DecodedTileComponents,crate::DecodeError>(error));
    part2_cold_bind(|events|part2_extraction_tile_calls_run(prepared,plan.components,planes,first.component_coding_styles,kernels,crate::codestream::image_size_component_count(size),crate::codestream::image_size_component_infos(size),
        first.multiple_component_transform,standard,work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),events),
        |effect:Part2ExtractionTileEffect,rest|Some((match effect.0{Err(error)=>Err(error),Ok(())=>Ok(Part2DecodedTileComponents {prepared:effect.1,mct_work:effect.2})},rest)),Ok(effect),Err(error));
    part2_decode_eta(|events|part2_planned_extraction_run(plan,first,size,standard,limits,prepared,work,precincts,events),Err(error));
    part2_cold_bind(|events|part2_packet_value_run(parts,plan.grid,plan.precincts,selection,limits,events),
        |decoded:(crate::packet::TilePacketDecode,Seq<Part1PacketPrecinctState>),rest|part2_planned_extraction_run(plan,first,size,standard,limits,prepared,work,decoded.1,rest),Ok((decoded,precincts)),Err(error));
}

pub(crate) open spec fn part2_tile_decode_run(size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>,
    caps: Option<(u32, Seq<u16>)>, discard: Option<u8>, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>,
    initial: (u64, u64, u64), work: u64, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2DecodedLayoutTile> {
    part2_jpip_snapshot_bind(part2_tile_metadata_run(parts,crate::codestream::image_size_component_count(size),discard,events),
        |metadata:Part2TileDecodeMetadata,rest|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_tile_decode_result(size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>,
    caps: Option<(u32, Seq<u16>)>, discard: Option<u8>, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>,
    initial: (u64, u64, u64), work: u64, result: Result<Part2DecodedLayoutTile, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_tile_decode_run(size, tile, parts, caps, discard, limits, prepared, initial, work, events), result)
}
pub(crate) proof fn part2_tile_decode_normal(size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>,
    caps: Option<(u32, Seq<u16>)>, discard: Option<u8>, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>,
    initial: (u64, u64, u64), work: u64)
    ensures part2_tile_decode_result(size, tile, parts, caps, discard, limits, prepared, initial, work,
        part2_decode_tile_parts_owned(size, tile, parts, caps, discard, limits, prepared, initial, work)),
{
    reveal(part2_tile_decode_result);
    let result = part2_decode_tile_parts_owned(size, tile, parts, caps, discard, limits, prepared, initial, work);
    let metadata=part2_tile_decode_metadata_owned(parts,crate::codestream::image_size_component_count(size),discard);
    part2_tile_metadata_normal(parts,crate::codestream::image_size_component_count(size),discard);
    part2_tile_metadata_frames(parts,crate::codestream::image_size_component_count(size),discard,metadata);
    if let Ok(value)=metadata {
        part2_tile_after_metadata_normal(size,tile,parts,caps,discard,limits,prepared,initial,work,value);
        part2_decode_eta(|events|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,value,events),result);
    }
    part2_cold_bind(|events|part2_tile_metadata_run(parts,crate::codestream::image_size_component_count(size),discard,events),
        |metadata:Part2TileDecodeMetadata,rest|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,rest),metadata,result);
}
pub(crate) proof fn part2_tile_decode_components_actual(size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>,
    caps: Option<(u32, Seq<u16>)>, discard: Option<u8>, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>,
    initial: (u64, u64, u64), work: u64, metadata: Part2TileDecodeMetadata, plan: Part2ProgressionTilePlan,
    counters: (u64, u64, u64), result: Result<Part2DecodedTileComponents, crate::DecodeError>)
    requires part2_tile_decode_metadata_owned(parts, crate::codestream::image_size_component_count(size), discard) == Ok(metadata),
        part2_progression_tile_plan_owned(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
            metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, match discard { None => 0u8, Some(levels) => levels }),
            (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps)), limits) == Ok(plan),
        part2_planned_tile_accounting(plan, match discard { None => None, Some(_) => Some(metadata.resolution_counts) }, initial, limits) == Ok(counters),
        part2_grid_plan_result(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,
            (tile,match discard {None=>0u8,Some(level)=>level}),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps)),limits,Ok(plan)),
        part2_tile_metadata_result(parts,crate::codestream::image_size_component_count(size),discard,Ok(metadata)),
        part2_planned_decode_result(plan, parts, metadata.first, size, metadata.standard, match discard { None => None, Some(_) => Some(metadata.resolution_counts) },
            limits, prepared, work, result),
    ensures part2_tile_decode_result(size, tile, parts, caps, discard, limits, prepared, initial, work, match result {
        Err(error) => Err(error), Ok(decoded) => Ok(Part2DecodedLayoutTile { prepared: decoded.prepared, counters, mct_work: decoded.mct_work }),
    }),
{
    reveal(part2_tile_decode_result); reveal(part2_planned_decode_result);
    let maximum = match discard { None => None, Some(_) => Some(metadata.resolution_counts) };
    let finish = |decoded: Part2DecodedTileComponents, rest| Some((Ok(Part2DecodedLayoutTile { prepared: decoded.prepared, counters, mct_work: decoded.mct_work }), rest));
    let final_result = match result { Err(error) => Err(error), Ok(decoded) => Ok(Part2DecodedLayoutTile { prepared: decoded.prepared, counters, mct_work: decoded.mct_work }) };
    if let Ok(value) = result { part2_cold_pure::<Part2DecodedLayoutTile>(Ok(Part2DecodedLayoutTile { prepared: value.prepared, counters, mct_work: value.mct_work })); }
    part2_cold_bind(|events| part2_planned_decode_run(plan, parts, metadata.first, size, metadata.standard, maximum, limits, prepared, work, events), finish, result, final_result);
    part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planned_decode_run(plan,parts,metadata.first,size,metadata.standard,maximum,limits,prepared,work,events),finish),final_result);
    reveal(part2_grid_plan_result);
    part2_grid_plan_frames(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,
        (tile,match discard {None=>0u8,Some(level)=>level}),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps)),limits,Ok(plan));
    part2_decode_eta(|events|part2_tile_after_grid_plan(size,parts,metadata,discard,limits,prepared,initial,work,plan,events),final_result);
    part2_cold_bind(|events|part2_grid_plan_run(size,metadata.first.coding_style,&metadata.first.component_coding_styles,metadata.first.component_quantizations,&metadata.first.roi_shifts,
        (tile,match discard {None=>0u8,Some(level)=>level}),(part2_profile_multiple_sets(caps),part2_profile_magnitude_bound(caps),part2_profile_force_ht(caps)),limits,events),
        |plan:Part2ProgressionTilePlan,rest|part2_tile_after_grid_plan(size,parts,metadata,discard,limits,prepared,initial,work,plan,rest),Ok(plan),final_result);
    part2_decode_eta(|events|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,events),final_result);
    part2_tile_metadata_frames(parts,crate::codestream::image_size_component_count(size),discard,Ok(metadata));
    part2_cold_bind(|events|part2_tile_metadata_run(parts,crate::codestream::image_size_component_count(size),discard,events),
        |metadata:Part2TileDecodeMetadata,rest|part2_tile_after_metadata_run(size,tile,parts,caps,discard,limits,prepared,initial,work,metadata,rest),Ok(metadata),final_result);
}
#[verifier::opaque]
pub(crate) open spec fn part2_full_decode_run(size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    limits: &crate::ResourceLimits, count: u64, tile: u64, before: Part2DecodedLayoutTile, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1DecodedImageModel>
    decreases if tile < count { count as int - tile as int } else { 0int },
{
    if tile >= count { Some((part2_assemble_prepared(crate::image::assembly_size_view(size), before.prepared, None, crate::limits::resource_decoded_bytes_limit(limits)), events)) }
    else if tile > u16::MAX as u64 { Some((Err(part1_block_placement_error(true)), events)) }
    else { match part2_collect_tile_parts(parts, tile as u16) {
        Err(error) => Some((Err(error), events)),
        Ok(selected) => part2_jpip_snapshot_bind(part2_tile_decode_run(size, tile as u16, selected, caps, None, limits, before.prepared, before.counters, before.mct_work, events),
            |after: Part2DecodedLayoutTile, rest| if tile == u64::MAX { Some((Err(part1_block_placement_error(true)), rest)) }
                else { part2_full_decode_run(size, parts, caps, limits, count, (tile + 1) as u64, after, rest) }),
    }}
}
pub(crate) proof fn part2_full_decode_step(size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    limits: &crate::ResourceLimits, count: u64, tile: u64, before: Part2DecodedLayoutTile, selected: Seq<Part2OwnedTilePart>)
    requires tile<count,tile<=u16::MAX as u64,part2_collect_tile_parts(parts,tile as u16)==Ok(selected),
    ensures forall|events| #[trigger] part2_full_decode_run(size,parts,caps,limits,count,tile,before,events)
        ==part2_jpip_snapshot_bind(part2_tile_decode_run(size,tile as u16,selected,caps,None,limits,before.prepared,before.counters,before.mct_work,events),
            |after:Part2DecodedLayoutTile,rest|part2_full_decode_run(size,parts,caps,limits,count,(tile+1) as u64,after,rest)),
{
    reveal_with_fuel(part2_full_decode_run,1);
}
pub(crate) proof fn part2_full_decode_normal(size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    limits: &crate::ResourceLimits, count: u64, tile: u64, before: Part2DecodedLayoutTile)
    ensures part2_cold_framed(|events| part2_full_decode_run(size, parts, caps, limits, count, tile, before, events),
        part2_full_layout_tiles(size, parts, caps, limits, count, tile, before)),
    decreases if tile < count { count as int - tile as int } else { 0int },
{
    reveal_with_fuel(part2_full_decode_run, 1); reveal_with_fuel(part2_full_layout_tiles, 1); reveal(part2_tile_decode_result);
    let result = part2_full_layout_tiles(size, parts, caps, limits, count, tile, before);
    if tile >= count || tile > u16::MAX as u64 { part2_cold_pure::<Part1DecodedImageModel>(result); }
    else { match part2_collect_tile_parts(parts, tile as u16) {
        Err(_) => { part2_cold_pure::<Part1DecodedImageModel>(result); },
        Ok(selected) => {
            part2_tile_decode_normal(size, tile as u16, selected, caps, None, limits, before.prepared, before.counters, before.mct_work);
            let decoded = part2_decode_tile_parts_owned(size, tile as u16, selected, caps, None, limits, before.prepared, before.counters, before.mct_work);
            if let Ok(after) = decoded {
                if tile == u64::MAX { part2_cold_pure::<Part1DecodedImageModel>(Err(part1_block_placement_error(true))); }
                else {
                    part2_full_decode_normal(size, parts, caps, limits, count, (tile + 1) as u64, after);
                    part2_decode_eta(|events|part2_full_decode_run(size,parts,caps,limits,count,(tile+1) as u64,after,events),
                        part2_full_layout_tiles(size,parts,caps,limits,count,(tile+1) as u64,after));
                }
            }
            part2_cold_bind(|events| part2_tile_decode_run(size, tile as u16, selected, caps, None, limits, before.prepared, before.counters, before.mct_work, events),
                |after: Part2DecodedLayoutTile, rest| if tile == u64::MAX { Some((Err(part1_block_placement_error(true)), rest)) }
                    else { part2_full_decode_run(size, parts, caps, limits, count, (tile + 1) as u64, after, rest) }, decoded, result);
        },
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_selected_decode_run(size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles: Seq<u16>, region: [u32; 4], discard: u8, limits: &crate::ResourceLimits, index: nat, before: Part2DecodedLayoutTile,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1DecodedImageModel>
    decreases if index < tiles.len() { (tiles.len() - index) as nat } else { 0nat },
{
    if index >= tiles.len() { Some((part2_assemble_prepared(crate::image::assembly_size_view(size), before.prepared, Some((region, discard)), crate::limits::resource_decoded_bytes_limit(limits)), events)) }
    else { match part2_collect_tile_parts(parts, tiles[index as int]) {
        Err(error) => Some((Err(error), events)),
        Ok(selected) => part2_jpip_snapshot_bind(part2_tile_decode_run(size, tiles[index as int], selected, caps, Some(discard), limits, before.prepared, before.counters, before.mct_work, events),
            |after: Part2DecodedLayoutTile, rest| part2_selected_decode_run(size, parts, caps, tiles, region, discard, limits, index + 1, after, rest)),
    }}
}
pub(crate) proof fn part2_selected_decode_step(size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles:Seq<u16>,region:[u32;4],discard:u8,limits:&crate::ResourceLimits,index:nat,before:Part2DecodedLayoutTile,selected:Seq<Part2OwnedTilePart>)
    requires index<tiles.len(),part2_collect_tile_parts(parts,tiles[index as int])==Ok(selected),
    ensures forall|events| #[trigger] part2_selected_decode_run(size,parts,caps,tiles,region,discard,limits,index,before,events)
        ==part2_jpip_snapshot_bind(part2_tile_decode_run(size,tiles[index as int],selected,caps,Some(discard),limits,before.prepared,before.counters,before.mct_work,events),
            |after:Part2DecodedLayoutTile,rest|part2_selected_decode_run(size,parts,caps,tiles,region,discard,limits,index+1,after,rest)),
{
    reveal_with_fuel(part2_selected_decode_run,1);
}
pub(crate) proof fn part2_selected_decode_normal(size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles: Seq<u16>, region: [u32; 4], discard: u8, limits: &crate::ResourceLimits, index: nat, before: Part2DecodedLayoutTile)
    ensures part2_cold_framed(|events| part2_selected_decode_run(size, parts, caps, tiles, region, discard, limits, index, before, events),
        part2_selected_layout_tiles(size, parts, caps, tiles, region, discard, limits, index, before)),
    decreases if index < tiles.len() { (tiles.len() - index) as nat } else { 0nat },
{
    reveal_with_fuel(part2_selected_decode_run, 1); reveal_with_fuel(part2_selected_layout_tiles, 1); reveal(part2_tile_decode_result);
    let result = part2_selected_layout_tiles(size, parts, caps, tiles, region, discard, limits, index, before);
    if index >= tiles.len() { part2_cold_pure::<Part1DecodedImageModel>(result); }
    else { match part2_collect_tile_parts(parts, tiles[index as int]) {
        Err(_) => { part2_cold_pure::<Part1DecodedImageModel>(result); },
        Ok(selected) => {
            let tile = tiles[index as int];
            part2_tile_decode_normal(size, tile, selected, caps, Some(discard), limits, before.prepared, before.counters, before.mct_work);
            let decoded = part2_decode_tile_parts_owned(size, tile, selected, caps, Some(discard), limits, before.prepared, before.counters, before.mct_work);
            if let Ok(after) = decoded {
                part2_selected_decode_normal(size, parts, caps, tiles, region, discard, limits, index + 1, after);
                part2_decode_eta(|events|part2_selected_decode_run(size,parts,caps,tiles,region,discard,limits,index+1,after,events),
                    part2_selected_layout_tiles(size,parts,caps,tiles,region,discard,limits,index+1,after));
            }
            part2_cold_bind(|events| part2_tile_decode_run(size, tile, selected, caps, Some(discard), limits, before.prepared, before.counters, before.mct_work, events),
                |after: Part2DecodedLayoutTile, rest| part2_selected_decode_run(size, parts, caps, tiles, region, discard, limits, index + 1, after, rest), decoded, result);
        },
    }}
}
}
