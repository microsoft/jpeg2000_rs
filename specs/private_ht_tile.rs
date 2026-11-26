use super::*;
verus! {

pub(crate) proof fn private_unit_result_fields(result:Result<(),crate::DecodeError>)
    ensures result.is_ok() ==> result==Ok(()),
{
    if let Ok(value)=result{assert(value==());}
}

pub(crate) open spec fn private_ht_eligible(
    size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,
    caps:Option<(u32,Seq<u16>)>,discard:Option<u8>,
) -> bool {
    if !crate::decode::PRIVATE_HT_PRIMARY_ENABLED
        || crate::codestream::image_size_component_count(size)!=1
        || parts.len()!=1 || (match discard{None=>false,Some(level)=>level!=0})
        || !part2_profile_force_ht(caps) { false }
    else {
        let first=parts[0];
        match crate::codestream::component_coding_style_result(&first.component_coding_styles,0) {
            Err(_)=>false,
            Ok(style)=>match crate::codestream::coding_style_tier1_result(style) {
                Err(_)=>false,
                Ok(tier1)=>match part2_roi_shift(crate::codestream::roi_shifts_view(&first.roi_shifts),0) {
                    Err(_)=>false,
                    Ok(roi)=>match part2_tile_component_bounds(
                        crate::codestream::selection_geometry_view(size),
                        crate::codestream::image_size_component_count(size),
                        crate::codestream::image_size_component_infos(size),first.tile_index,0,
                    ) {
                        Err(_)=>false,
                        Ok(bounds)=>match part2_resolution_geometry(
                            crate::codestream::selection_geometry_view(size),
                            crate::codestream::image_size_component_count(size),
                            crate::codestream::image_size_component_infos(size),
                            crate::decode::resolution_geometry_style(style),0,0,Some(tile),
                        ){
                        Err(_)=>false,
                        Ok(geometry)=>matches!(tier1.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput)
                            && first.tile_index==tile && style.decomposition_levels==0
                            && style.decomposition_structure.is_none() && !style.precincts_defined
                            && !matches!(style.transform,crate::codestream::WaveletTransform::Arbitrary(_))
                            && !first.coding_style.multiple_component_transform
                            && first.multiple_component_transform.is_none()
                            && first.progression_changes.len()==0
                            && matches!(first.packed_packet_headers.source,Part1PackedHeaderSource::None)
                            && matches!(first.packet_lengths.source,Part1PacketLengthSource::None)
                            && roi==0 && !first.has_roi_marker
                            && bounds.x0==0 && bounds.y0==0
                            && 0<bounds.x1<=32768 && 0<bounds.y1<=32768
                            && geometry.precincts==1 && geometry.precincts_across==1 && geometry.precincts_down==1,
                        },
                    },
                },
            },
        }
    }
}

pub struct PrivateHtDecoderState {
    pub logical:Tier1DecoderState,
    pub packed:bool,
}

pub(crate) open spec fn private_ht_metadata_supported(state:Tier1DecoderState)->bool {
    state.private_plan
        && matches!(state.style.block_coding,crate::tier1::Tier1BlockCoding::HighThroughput)
        && state.style.force_high_throughput
        && state.bitplane_state.is_none() && state.mq_context_state.is_none()
        && !state.reset_contexts_before_mq && state.legacy_segment.is_none()
        && state.legacy_decode_work==0
}

pub struct PrivateHtPrecinctState {
    pub logical:Part1PacketPrecinctState,
    pub packed:Seq<bool>,
}

pub(crate) open spec fn private_ht_precinct_planes(precincts:Seq<PrivateHtPrecinctState>)->Seq<Seq<Tier1RawPlane>> {
    precincts.map_values(|precinct:PrivateHtPrecinctState|
        precinct.logical.decoders.map_values(|decoder:Tier1DecoderState|decoder.plane))
}

pub(crate) proof fn private_ht_selected_metadata(size:&crate::codestream::ImageSize,tile:u16,parts:Seq<Part2OwnedTilePart>,
    caps:Option<(u32,Seq<u16>)>,discard:Option<u8>,metadata:Part2TileDecodeMetadata)
    requires private_ht_eligible(size,tile,parts,caps,discard),
        part2_tile_decode_metadata_owned(parts,crate::codestream::image_size_component_count(size),discard)==Ok(metadata),
    ensures metadata.first==parts[0],
        private_ht_eligible(size,tile,parts,caps,None),
        metadata.standard.0==false,
        metadata.resolution_counts==match discard{None=>Seq::empty(),Some(_)=>seq![1u8]},
{
    reveal_with_fuel(part2_selected_tile_resolutions,2);
}
}
