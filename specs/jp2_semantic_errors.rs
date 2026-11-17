//! Ordinary header semantics cannot manufacture a storage-refusal response.
use super::*;
verus! {
pub(crate) proof fn part2_box_semantic_errors(reader:Part2BoxReaderState)
    ensures match part2_box_reader_next_ref(reader).0 {
        Some(Err(error))=>error!=crate::DecodeError::AllocationFailed,_=>true,
    },
{
    reveal(part2_box_reader_next);reveal(part2_box_reader_after_work);reveal(part2_box_reader_after_header);
}
pub(crate) proof fn part2_palette_word_semantic_errors(bytes:Seq<u8>,base:u64,count:nat)
    ensures part2_palette_word_prefix(bytes,base,count)!=Err(crate::DecodeError::AllocationFailed),
        part2_palette_modulus_prefix(base,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_palette_word_prefix,1);reveal_with_fuel(part2_palette_modulus_prefix,1);
    if count>0{part2_palette_word_semantic_errors(bytes,base,(count-1) as nat);}
}
pub(crate) proof fn part2_palette_descriptors_semantic_errors(input:Part2BoxReference,base:u64,count:nat)
    ensures part2_palette_descriptors(input,base,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_palette_descriptors,1);
    if count>0{part2_palette_descriptors_semantic_errors(input,base,(count-1) as nat);}
}
pub(crate) proof fn part2_palette_row_semantic_errors(input:Part2BoxReference,base:u64,columns:Seq<crate::jp2::PaletteColumn>,
    initial:Part2PaletteValues,count:nat)
    ensures part2_palette_row(input,base,columns,initial,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_palette_row,1);reveal(part2_parse_palette_value);
    if count>0{
        part2_palette_row_semantic_errors(input,base,columns,initial,(count-1) as nat);
        if let Ok(previous)=part2_palette_row(input,base,columns,initial,(count-1) as nat){
            let index=(count-1) as nat;
            if index<columns.len(){
                let descriptor=columns[index as int];
                let end=previous.1 as nat+(descriptor.precision as nat+7)/8;
                let bytes=input.1.subrange(previous.1 as int,end as int);
                part2_palette_word_semantic_errors(bytes,base,bytes.len());
                part2_palette_word_semantic_errors(bytes,base,descriptor.precision as nat);
            }
        }
    }
}
pub(crate) proof fn part2_palette_rows_semantic_errors(input:Part2BoxReference,base:u64,columns:Seq<crate::jp2::PaletteColumn>,count:nat)
    ensures part2_palette_rows(input,base,columns,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_palette_rows,1);
    if count>0{
        part2_palette_rows_semantic_errors(input,base,columns,(count-1) as nat);
        if let Ok(initial)=part2_palette_rows(input,base,columns,(count-1) as nat){
            part2_palette_row_semantic_errors(input,base,columns,initial,columns.len());
        }
    }
}
pub(crate) proof fn part2_palette_semantic_errors(input:Part2BoxReference,base:u64)
    ensures part2_parse_palette(input,base)!=Err(crate::DecodeError::AllocationFailed),
{
    reveal(part2_parse_palette);
    part2_palette_descriptors_semantic_errors(input,base,input.1[2] as nat);
    if let Ok(descriptors)=part2_palette_descriptors(input,base,input.1[2] as nat){
        part2_palette_rows_semantic_errors(input,base,descriptors.0,part2_box_u16([input.1[0],input.1[1]]) as nat);
    }
}
pub(crate) proof fn part2_channel_semantic_errors(input:Part2BoxReference,channels:u16,base:u64,count:nat)
    ensures part2_channel_records_prefix(input,channels,base,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_channel_records_prefix,1);
    if count>0{part2_channel_semantic_errors(input,channels,base,(count-1) as nat);}
}
pub(crate) proof fn part2_mapping_semantic_errors(input:Part2BoxReference,components:u16,columns:u8,base:u64,count:nat)
    ensures part2_mapping_prefix(input,components,columns,base,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_mapping_prefix,1);
    if count>0{part2_mapping_semantic_errors(input,components,columns,base,(count-1) as nat);}
}
pub(crate) proof fn part2_bpcc_semantic_errors(input:Part2BoxReference,base:u64,count:nat)
    ensures part2_bpcc_prefix(input,base,count)!=Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_bpcc_prefix,1);
    if count>0{part2_bpcc_semantic_errors(input,base,(count-1) as nat);}
}
pub(crate) proof fn part2_resolution_semantic_errors(payload:Seq<u8>,reader:Part2BoxReaderState,base:u64,
    capture:Option<crate::jp2::Resolution>,display:Option<crate::jp2::Resolution>)
    ensures part2_resolution_boxes(payload,reader,base,capture,display)!=Err(crate::DecodeError::AllocationFailed),
    decreases payload.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_resolution_boxes,1);part2_box_semantic_errors(reader);
    let next=part2_box_reader_next_ref(reader);
    if let Some(Ok(input))=next.0{
        if reader.position<next.1.position && next.1.position<=payload.len(){
            if input.0.0==crate::jp2::BoxType::CAPTURE_RESOLUTION{
                if capture.is_none(){
                    if let Ok(value)=part2_parse_resolution(input,base){
                        part2_resolution_semantic_errors(payload,next.1,base,Some(value),display);
                    }
                }
            }else if input.0.0==crate::jp2::BoxType::DISPLAY_RESOLUTION{
                if display.is_none(){
                    if let Ok(value)=part2_parse_resolution(input,base){
                        part2_resolution_semantic_errors(payload,next.1,base,capture,Some(value));
                    }
                }
            }else{part2_resolution_semantic_errors(payload,next.1,base,capture,display);}
        }
    }
}
pub(crate) proof fn part2_raw_header_step_semantic_errors(input:Part2BoxReference,state:Part2RawHeaderState,limits:crate::ResourceLimits,base:u64)
    ensures part2_raw_header_step(input,state,limits,base)!=Err(crate::DecodeError::AllocationFailed),
{
    reveal(part2_raw_header_step);reveal(part2_parse_color_specification);reveal(part2_validate_color_specification_prefix);
    let kind=input.0.0;
    if kind==crate::jp2::BoxType::BITS_PER_COMPONENT{part2_bpcc_semantic_errors(input,base,input.1.len());}
    else if kind==crate::jp2::BoxType::PALETTE{part2_palette_semantic_errors(input,base);}
    else if kind==crate::jp2::BoxType::COMPONENT_MAPPING{
        let columns=match state.palette{None=>0nat,Some(value)=>value.1.len()};
        part2_mapping_semantic_errors(input,state.image.components,columns as u8,base,input.1.len()/4);
    }else if kind==crate::jp2::BoxType::CHANNEL_DEFINITION{
        let channels=if state.mappings.len()==0{state.image.components as nat}else{state.mappings.len()};
        part2_channel_semantic_errors(input,channels as u16,base,part2_box_u16([input.1[0],input.1[1]]) as nat);
    }else if kind==crate::jp2::BoxType::RESOLUTION{
        if let Ok(relative)=part2_box_payload_offset(input.0){
            if let Ok(nested)=part2_box_add_offset(base,relative){
                if let Ok(reader)=part2_box_reader_from_input(input.1,limits){
                    part2_resolution_semantic_errors(input.1,reader,nested,None,None);
                }
            }
        }
    }
}
pub(crate) proof fn part2_raw_header_boxes_semantic_errors(payload:Seq<u8>,reader:Part2BoxReaderState,state:Part2RawHeaderState,
    limits:crate::ResourceLimits,base:u64,allow:bool)
    ensures part2_raw_header_boxes(payload,reader,state,limits,base,allow)!=Err(crate::DecodeError::AllocationFailed),
    decreases payload.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_raw_header_boxes,1);part2_box_semantic_errors(reader);
    let next=part2_box_reader_next_ref(reader);
    if let Some(Ok(input))=next.0{
        if reader.position<next.1.position && next.1.position<=payload.len() && state.nested<u32::MAX{
            let prepared=Part2RawHeaderState {nested:(state.nested+1) as u32,..state};
            part2_raw_header_step_semantic_errors(input,prepared,limits,base);
            if let Ok(updated)=part2_raw_header_step(input,prepared,limits,base){
                part2_raw_header_boxes_semantic_errors(payload,next.1,updated,limits,base,allow);
            }
        }
    }
}
pub(crate) proof fn part2_jp2_header_semantic_errors(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool)
    ensures part2_parse_jp2_header_profile(payload,limits,base,allow)!=Err(crate::DecodeError::AllocationFailed),
{
    reveal(part2_parse_image_header);
    if let Ok(reader)=part2_box_reader_from_input(payload,limits){part2_box_semantic_errors(reader);}
    if let Ok((reader,state))=part2_jp2_header_storage_start(payload,limits,base){
        part2_raw_header_boxes_semantic_errors(payload,reader,state,limits,base,allow);
    }
}
}
