use super::{Part1PacketGrid, Part1PacketPrecinctState, ht_reader_error};
use vstd::prelude::*;

verus! {

pub struct Part1TilePacketPreparation {
    pub tile_index:u16,
    pub index:usize,
    pub payload_bytes:u64,
    pub packed_payload_bytes:u64,
    pub declared_packets:u64,
    pub all_lengths:bool,
    pub packed:Seq<Seq<u8>>,
}

pub struct Part1TilePacketCaps {
    pub work:u64,
    pub header:u64,
    pub blocks:u64,
    pub passes:u32,
    pub bytes:u64,
    pub input:u64,
}

pub struct Part1TilePacketParameters {
    pub parts:Seq<super::Part2OwnedTilePart>,
    pub grid:Part1PacketGrid,
    pub input:Part1TilePacketPreparation,
    pub selection:Option<Seq<u8>>,
    pub caps:Part1TilePacketCaps,
}

pub struct Part1TilePacketProgress {
    pub iterator:super::Part1ProgressionPacketIterator,
    pub length_iterator:super::Part1PacketLengthIter,
    pub current_tile_part:usize,
    pub length_tile_part:usize,
    pub offset:usize,
    pub packed_offset:usize,
    pub packets:u64,
    pub present_packets:u64,
    pub contributions:u64,
    pub segments:u64,
    pub passes:u64,
    pub packet_header_bytes:u64,
    pub packet_body_bytes:u64,
    pub seen:Seq<bool>,
    pub remaining_packets:u64,
}

pub struct Part1TilePacketExecution {
    pub progress:Part1TilePacketProgress,
    pub precincts:Seq<Part1PacketPrecinctState>,
}

pub open spec fn part1_tile_progress_initial(params:Part1TilePacketParameters)
    -> Result<Part1TilePacketProgress,crate::DecodeError> {
    if params.parts.len()==0 {Err(ht_reader_error(crate::MalformedKind::InvalidTilePart))}
    else {
        let first=params.parts[0];
        match super::part1_progression_iterator_initial(params.grid,first.coding_style.progression_order,
            first.progression_changes,params.caps.work) {
            Err(error)=>Err(error),
            Ok(iterator)=>if params.grid.packet_count as nat>usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else {Ok(Part1TilePacketProgress {
                iterator,length_iterator:super::part1_packet_lengths_iter(first.packet_lengths),
                current_tile_part:0,length_tile_part:0,offset:0,packed_offset:0,packets:0,present_packets:0,
                contributions:0,segments:0,passes:0,packet_header_bytes:0,packet_body_bytes:0,
                seen:Seq::new(params.grid.packet_count as nat,|i:int|false),remaining_packets:params.caps.work,
            })},
        }
    }
}

pub open spec fn part1_tile_length_present(part:crate::codestream::TilePartPayload<'_>)->bool {
    part1_tile_length_present_owned(crate::codestream::tile_part_owned_view(&part))
}

pub open spec fn part1_tile_length_present_owned(part:super::Part2OwnedTilePart)->bool {
    !matches!(part.packet_lengths.source,super::Part1PacketLengthSource::None)
}

#[verifier::opaque]
pub open spec fn part1_tile_boundary_scan(params:Part1TilePacketParameters,p:Part1TilePacketProgress)
    -> (Result<(),crate::DecodeError>,Part1TilePacketProgress)
    decreases params.parts.len()-p.current_tile_part as nat,
{
    if p.current_tile_part>=params.parts.len() {(Ok(()),p)}
    else if p.current_tile_part>=params.input.packed.len() {(Err(ht_reader_error(crate::MalformedKind::InvalidTilePart)),p)}
    else {
        let part=params.parts[p.current_tile_part as int];
        let packed=params.input.packed[p.current_tile_part as int];
        if p.offset<part.data.len() || p.packed_offset<packed.len() {(Ok(()),p)}
        else if p.offset!=part.data.len() || p.packed_offset!=packed.len() {
            (Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::ArithmeticOverflow)),p)
        } else {
            let length=if part1_tile_length_present_owned(part) && p.length_tile_part==p.current_tile_part {
                let next=super::part1_packet_length_next(p.length_iterator);
                let p=Part1TilePacketProgress {length_iterator:next.1,..p};
                match next.0 {
                    Err(error)=>(Err(error),p),
                    Ok(Some(_))=>(Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::InvalidPacketLength)),p),
                    Ok(None)=>(Ok(()),p),
                }
            } else {(Ok(()),p)};
            match length.0 {
                Err(_)=>length,
                Ok(())=>if length.1.current_tile_part==usize::MAX {(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),length.1)}
                    else {part1_tile_boundary_scan(params,Part1TilePacketProgress {
                        current_tile_part:(length.1.current_tile_part+1) as usize,offset:0,packed_offset:0,..length.1
                    })},
            }
        }
    }
}

pub open spec fn part1_tile_boundary_frame(original:Part1TilePacketProgress,updated:Part1TilePacketProgress)
    ->Part1TilePacketProgress {
    Part1TilePacketProgress {
        current_tile_part:updated.current_tile_part,length_iterator:updated.length_iterator,
        offset:updated.offset,packed_offset:updated.packed_offset,..original
    }
}

pub open spec fn part1_tile_boundary(params:Part1TilePacketParameters,p:Part1TilePacketProgress)
    -> (Result<(bool,bool),crate::DecodeError>,Part1TilePacketProgress) {
    let previous=p.current_tile_part;
    let raw=part1_tile_boundary_scan(params,p);
    let scanned=(raw.0,part1_tile_boundary_frame(p,raw.1));
    match scanned.0 {
        Err(error)=>(Err(error),scanned.1),
        Ok(())=>if previous==scanned.1.current_tile_part {(Ok((false,true)),scanned.1)}
        else if scanned.1.current_tile_part>=params.parts.len() {(Ok((true,false)),scanned.1)}
        else {
            let part=params.parts[scanned.1.current_tile_part as int];
            match super::part1_progression_iterator_initial(params.grid,part.coding_style.progression_order,
                part.progression_changes,params.caps.work) {
                Err(error)=>(Err(error),scanned.1),
                Ok(iterator)=>(Ok((true,true)),Part1TilePacketProgress {iterator,..scanned.1}),
            }
        },
    }
}

pub open spec fn part1_tile_packet_length(
    part:crate::codestream::TilePartPayload<'_>,p:Part1TilePacketProgress,
) -> (Result<Option<u32>,crate::DecodeError>,Part1TilePacketProgress) {
    part1_tile_packet_length_owned(crate::codestream::tile_part_owned_view(&part),p)
}

pub open spec fn part1_tile_packet_length_owned(
    part:super::Part2OwnedTilePart,p:Part1TilePacketProgress,
) -> (Result<Option<u32>,crate::DecodeError>,Part1TilePacketProgress) {
    let p=if p.length_tile_part!=p.current_tile_part {Part1TilePacketProgress {
        length_iterator:super::part1_packet_lengths_iter(part.packet_lengths),
        length_tile_part:p.current_tile_part,..p
    }}else{p};
    if !part1_tile_length_present_owned(part) {(Ok(None),p)}
    else {
        let next=super::part1_packet_length_next(p.length_iterator);
        let p=Part1TilePacketProgress {length_iterator:next.1,..p};
        match next.0 {
            Err(error)=>(Err(error),p),
            Ok(None)=>(Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::InvalidPacketLength)),p),
            Ok(Some(value))=>(Ok(Some(value)),p),
        }
    }
}

pub open spec fn part1_packet_context_layer(context:crate::packet::CodeBlockPacketContext,layer:u16)
    ->crate::packet::CodeBlockPacketContext {
    crate::packet::CodeBlockPacketContext {layer,..context}
}

pub open spec fn part1_packet_context_layers(contexts: Seq<crate::packet::CodeBlockPacketContext>, layer: u16)
    -> (Result<(), crate::DecodeError>, Seq<crate::packet::CodeBlockPacketContext>) {
    (Ok(()), contexts.map_values(|context: crate::packet::CodeBlockPacketContext| part1_packet_context_layer(context, layer)))
}

pub open spec fn part1_precinct_context_layer(state:Part1PacketPrecinctState,layer:u16)
    ->Part1PacketPrecinctState {
    Part1PacketPrecinctState {contexts:state.contexts.map_values(|context:crate::packet::CodeBlockPacketContext|
        part1_packet_context_layer(context,layer)),..state}
}

pub open spec fn part1_tile_precinct_packet(
    params:Part1TilePacketParameters,part:crate::codestream::TilePartPayload<'_>,p:Part1TilePacketProgress,
    coordinate:crate::packet::PacketCoordinate,expected:Option<u32>,precinct:Part1PacketPrecinctState,
) -> super::Part1PrecinctPayloadResult {
    part1_tile_precinct_packet_owned(params,crate::codestream::tile_part_owned_view(&part),p,coordinate,expected,precinct)
}

pub open spec fn part1_tile_precinct_packet_owned(
    params:Part1TilePacketParameters,part:super::Part2OwnedTilePart,p:Part1TilePacketProgress,
    coordinate:crate::packet::PacketCoordinate,expected:Option<u32>,precinct:Part1PacketPrecinctState,
) -> super::Part1PrecinctPayloadResult {
    let precinct=part1_precinct_context_layer(precinct,coordinate.layer);
    if p.current_tile_part>=params.input.packed.len() {(Err(ht_reader_error(crate::MalformedKind::InvalidTilePart)),precinct)}
    else if params.selection.is_some() && coordinate.component as nat>=params.selection.unwrap().len() {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle)),precinct)
    }else{
        let decode=match params.selection {None=>true,Some(counts)=>coordinate.resolution<counts[coordinate.component as int]};
        super::part1_precinct_packet_owned(precinct,part,p.offset,params.input.packed[p.current_tile_part as int],
            p.packed_offset,expected,(p.packets & 65535u64) as u16,decode,params.caps.blocks,params.caps.header,
            params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work)
    }
}

pub open spec fn part1_tile_account(
    p:Part1TilePacketProgress,decoded:crate::packet::PacketBodyDecode,tile_bytes:usize,packed_bytes:usize,
    expected:Option<u32>,seen_index:usize,
) -> (Result<(),crate::DecodeError>,Part1TilePacketProgress) {
    let a=if seen_index>=p.seen.len() || decoded.bytes_consumed==0 {
        (Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::InvalidPacketHeader)),p)
    }else if expected.is_some() && decoded.bytes_consumed!=expected.unwrap() {
        (Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::InvalidPacketLength)),p)
    }else if p.offset as nat+tile_bytes as nat>usize::MAX {
        (Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::ArithmeticOverflow)),p)
    }else{(Ok(()),Part1TilePacketProgress {offset:(p.offset+tile_bytes) as usize,..p})};
    let b=match a.0 {
        Err(_)=>a,
        Ok(())=>if a.1.packed_offset as nat+packed_bytes as nat>usize::MAX {
            (Err(super::part1_packet_reader_error(a.1.offset,crate::MalformedKind::ArithmeticOverflow)),a.1)
        }else{(Ok(()),Part1TilePacketProgress {packed_offset:(a.1.packed_offset+packed_bytes) as usize,..a.1})},
    };
    let c=match b.0 {
        Err(_)=>b,
        Ok(())=>if b.1.packets==u64::MAX {(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),b.1)}
            else{(Ok(()),Part1TilePacketProgress {packets:(b.1.packets+1) as u64,seen:b.1.seen.update(seen_index as int,true),..b.1})},
    };
    let d=match c.0 {
        Err(_)=>c,
        Ok(())=>if c.1.present_packets as nat+if decoded.present {1nat}else{0nat}>u64::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),c.1)
        }else{(Ok(()),Part1TilePacketProgress {present_packets:(c.1.present_packets+if decoded.present {1u64}else{0u64}) as u64,..c.1})},
    };
    let e=match d.0 {
        Err(_)=>d,
        Ok(())=>if d.1.contributions as nat+decoded.contributions as nat>u64::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),d.1)
        }else{(Ok(()),Part1TilePacketProgress {contributions:(d.1.contributions+decoded.contributions) as u64,..d.1})},
    };
    let f=match e.0 {
        Err(_)=>e,
        Ok(())=>if e.1.segments as nat+decoded.segments as nat>u64::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),e.1)
        }else{(Ok(()),Part1TilePacketProgress {segments:(e.1.segments+decoded.segments) as u64,..e.1})},
    };
    let g=match f.0 {
        Err(_)=>f,
        Ok(())=>if f.1.passes as nat+decoded.passes as nat>u64::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),f.1)
        }else{(Ok(()),Part1TilePacketProgress {passes:(f.1.passes+decoded.passes) as u64,..f.1})},
    };
    let h=match g.0 {
        Err(_)=>g,
        Ok(())=>if g.1.packet_header_bytes as nat+decoded.header_bytes as nat>u64::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),g.1)
        }else{(Ok(()),Part1TilePacketProgress {packet_header_bytes:(g.1.packet_header_bytes+decoded.header_bytes) as u64,..g.1})},
    };
    match h.0 {
        Err(_)=>h,
        Ok(())=>if h.1.packet_body_bytes as nat+decoded.body_bytes as nat>u64::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),h.1)
        }else{(Ok(()),Part1TilePacketProgress {packet_body_bytes:(h.1.packet_body_bytes+decoded.body_bytes) as u64,..h.1})},
    }
}

pub open spec fn part1_tile_all_seen(seen:Seq<bool>)->bool {
    forall |i:int| 0<=i<seen.len() ==> seen[i]
}

pub open spec fn part1_tile_packet_slot(grid:Part1PacketGrid,coordinate:crate::packet::PacketCoordinate)
    -> Result<(usize,usize),crate::DecodeError> {
    match super::part1_packet_grid_precinct_index(grid,coordinate.component,coordinate.resolution,coordinate.precinct) {
        Err(error)=>Err(error),
        Ok(index)=>if index as nat*grid.layers as nat+coordinate.layer as nat>usize::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        }else{Ok((index,(index as nat*grid.layers as nat+coordinate.layer as nat) as usize))},
    }
}

pub open spec fn part1_tile_omit_packet(
    params:Part1TilePacketParameters,p:Part1TilePacketProgress,
    coordinate:crate::packet::PacketCoordinate,precinct_count:usize,
) -> (Result<(),crate::DecodeError>,Part1TilePacketProgress) {
    match part1_tile_packet_slot(params.grid,coordinate) {
        Err(error)=>(Err(error),p),
        Ok((index,seen))=>if index>=precinct_count || seen>=p.seen.len() {
            (Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::InvalidPacketHeader)),p)
        }else{(Ok(()),Part1TilePacketProgress {seen:p.seen.update(seen as int,true),..p})},
    }
}

pub open spec fn part1_tile_packet(
    params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate,
) -> (Result<(),crate::DecodeError>,Part1TilePacketExecution) {
    if s.progress.current_tile_part>=params.parts.len() {
        (Err(crate::DecodeError::MalformedInput {offset:params.input.payload_bytes,kind:crate::MalformedKind::Truncated}),s)
    }else{
        let part=params.parts[s.progress.current_tile_part as int];
        let slot=part1_tile_packet_slot(params.grid,coordinate);
        let duplicate=match slot {
            Err(_)=>false,
            Ok((_,seen))=>seen<s.progress.seen.len() && s.progress.seen[seen as int],
        };
        if duplicate {(Ok(()),s)}else{
        let length=part1_tile_packet_length_owned(part,s.progress);
        let s=Part1TilePacketExecution {progress:length.1,..s};
        match length.0 {
            Err(error)=>(Err(error),s),
            Ok(expected)=>match slot {
                Err(error)=>(Err(error),s),
                Ok((index,seen))=>{
                    if seen>=s.progress.seen.len() {(Err(super::part1_packet_reader_error(s.progress.offset,crate::MalformedKind::InvalidPacketHeader)),s)}
                    else if s.progress.seen[seen as int] {(Ok(()),s)}
                    else if index>=s.precincts.len() {(Err(super::part1_packet_reader_error(s.progress.offset,crate::MalformedKind::InvalidPacketHeader)),s)}
                    else{
                            let packet=part1_tile_precinct_packet_owned(params,part,s.progress,coordinate,expected,s.precincts[index as int]);
                            let s=Part1TilePacketExecution {precincts:s.precincts.update(index as int,packet.1),..s};
                            match packet.0 {
                                Err(error)=>(Err(error),s),
                                Ok((decoded,tile_bytes,packed_bytes))=>{
                                    let account=part1_tile_account(s.progress,decoded,tile_bytes,packed_bytes,expected,seen);
                                    (account.0,Part1TilePacketExecution {progress:account.1,..s})
                                },
                        }
                    }
                },
            },
        }
        }
    }
}

pub open spec fn part1_tile_iteration(
    params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate,
) -> (Result<bool,crate::DecodeError>,Part1TilePacketExecution) {
    if s.progress.remaining_packets==0 {(Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange)),s)}
    else {
        let s=Part1TilePacketExecution {progress:Part1TilePacketProgress {
            remaining_packets:(s.progress.remaining_packets-1) as u64,..s.progress
        },..s};
        if s.progress.current_tile_part==params.parts.len() {
            let omitted=part1_tile_omit_packet(params,s.progress,coordinate,s.precincts.len() as usize);
            (match omitted.0 {Err(error)=>Err(error),Ok(())=>Ok(true)},
                Part1TilePacketExecution {progress:omitted.1,..s})
        }else{
        let boundary=part1_tile_boundary(params,s.progress);
        let s=Part1TilePacketExecution {progress:boundary.1,..s};
        match boundary.0 {
            Err(error)=>(Err(error),s),
            Ok((changed,more))=>if changed {
                if more {(Ok(true),s)}else{
                    let omitted=part1_tile_omit_packet(params,s.progress,coordinate,s.precincts.len() as usize);
                    (match omitted.0 {Err(error)=>Err(error),Ok(())=>Ok(true)},
                        Part1TilePacketExecution {progress:omitted.1,..s})
                }
            }
                else{
                    let packet=part1_tile_packet(params,s,coordinate);
                    (match packet.0 {Err(error)=>Err(error),Ok(())=>Ok(true)},packet.1)
                },
        }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_tile_run(params:Part1TilePacketParameters,s:Part1TilePacketExecution)
    -> (Result<(),crate::DecodeError>,Part1TilePacketExecution)
    decreases s.progress.remaining_packets,
{
    let next=super::part1_progression_iterator_next(s.progress.iterator);
    let s=Part1TilePacketExecution {progress:Part1TilePacketProgress {iterator:next.1,..s.progress},..s};
    match next.0 {
        Err(error)=>(Err(error),s),
        Ok(None)=>(Ok(()),s),
        Ok(Some(coordinate))=>{
            let iteration=part1_tile_iteration(params,s,coordinate);
            match iteration.0 {
                Err(error)=>(Err(error),iteration.1),
                Ok(false)=>(Ok(()),iteration.1),
                Ok(true)=>part1_tile_run(params,iteration.1),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_tile_finish_scan(params:Part1TilePacketParameters,p:Part1TilePacketProgress)
    -> (Result<(),crate::DecodeError>,Part1TilePacketProgress)
    decreases params.parts.len()-p.current_tile_part as nat,
{
    if p.current_tile_part>=params.parts.len() {(Ok(()),p)}
    else if p.current_tile_part>=params.input.packed.len() {(Err(ht_reader_error(crate::MalformedKind::InvalidTilePart)),p)}
    else {
        let part=params.parts[p.current_tile_part as int];
        let packed=params.input.packed[p.current_tile_part as int];
        if p.offset!=part.data.len() || p.packed_offset!=packed.len() {
            (Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::TrailingData)),p)
        }else{
            let length=if part1_tile_length_present_owned(part) && p.length_tile_part==p.current_tile_part {
                let next=super::part1_packet_length_next(p.length_iterator);
                let p=Part1TilePacketProgress {length_iterator:next.1,..p};
                match next.0 {
                    Err(error)=>(Err(error),p),
                    Ok(Some(_))=>(Err(super::part1_packet_reader_error(p.offset,crate::MalformedKind::InvalidPacketLength)),p),
                    Ok(None)=>(Ok(()),p),
                }
            }else{(Ok(()),p)};
            match length.0 {
                Err(_)=>length,
                Ok(())=>if length.1.current_tile_part==usize::MAX {(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),length.1)}
                    else{part1_tile_finish_scan(params,Part1TilePacketProgress {
                        current_tile_part:(length.1.current_tile_part+1) as usize,offset:0,packed_offset:0,..length.1
                    })},
            }
        }
    }
}

pub open spec fn part1_tile_finish(params:Part1TilePacketParameters,p:Part1TilePacketProgress)
    -> (Result<crate::packet::TilePacketDecode,crate::DecodeError>,Part1TilePacketProgress) {
    let scan=part1_tile_finish_scan(params,p);
    match scan.0 {
        Err(error)=>(Err(error),scan.1),
        Ok(())=>if scan.1.packets!=params.grid.packet_count
            && (scan.1.packets>params.grid.packet_count || scan.1.packets==0
                || scan.1.seen.len()!=params.grid.packet_count as nat
                || !part1_tile_all_seen(scan.1.seen)) {
            (Err(crate::DecodeError::MalformedInput {offset:params.input.payload_bytes,kind:crate::MalformedKind::Truncated}),scan.1)
        }else if params.input.all_lengths && scan.1.packets!=params.input.declared_packets {
            (Err(super::part1_packet_reader_error(0,crate::MalformedKind::InvalidPacketLength)),scan.1)
        }else if params.parts.len()>u32::MAX {(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),scan.1)}
        else{(Ok(crate::packet::TilePacketDecode {
            tile_index:params.input.tile_index,tile_parts:params.parts.len() as u32,packets:scan.1.packets,
            present_packets:scan.1.present_packets,contributions:scan.1.contributions,segments:scan.1.segments,
            passes:scan.1.passes,packet_header_bytes:scan.1.packet_header_bytes,packet_body_bytes:scan.1.packet_body_bytes,
            payload_bytes:params.input.payload_bytes,
        }),scan.1)},
    }
}

pub open spec fn part1_progression_tile_decode(
    parts:Seq<crate::codestream::TilePartPayload<'_>>,grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
) -> (Result<crate::packet::TilePacketDecode,crate::DecodeError>,Seq<Part1PacketPrecinctState>) {
    part1_progression_tile_decode_owned(crate::codestream::tile_parts_owned_view(parts),grid,precincts,selection,limits)
}

pub open spec fn part1_progression_tile_decode_owned(
    parts:Seq<super::Part2OwnedTilePart>,grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
) -> (Result<crate::packet::TilePacketDecode,crate::DecodeError>,Seq<Part1PacketPrecinctState>) {
    match part1_progression_tile_input_owned(parts,grid,precincts,selection,limits) {
        Err(error)=>(Err(error),precincts),
        Ok(input)=>{
            let params=Part1TilePacketParameters {parts,grid,input,selection,caps:Part1TilePacketCaps {
                work:crate::limits::resource_work_limit(limits),header:crate::limits::resource_packet_header_byte_limit(limits),
                blocks:crate::limits::resource_code_block_limit(limits),passes:crate::limits::resource_code_block_pass_limit(limits),
                bytes:crate::limits::resource_code_block_byte_limit(limits),input:crate::limits::resource_input_byte_limit(limits),
            }};
            match part1_tile_progress_initial(params) {
                Err(error)=>(Err(error),precincts),
                Ok(progress)=>{
                    let run=part1_tile_run(params,Part1TilePacketExecution {progress,precincts});
                    match run.0 {
                        Err(error)=>(Err(error),run.1.precincts),
                        Ok(())=>(part1_tile_finish(params,run.1.progress).0,run.1.precincts),
                    }
                },
            }
        },
    }
}

pub open spec fn part1_progression_resolution_levels(
    first:&crate::codestream::TilePartPayload<'_>,components:u16,index:u16,maximum:u8,
) -> Result<u8,crate::DecodeError> {
    part1_progression_resolution_levels_owned(crate::codestream::tile_part_owned_view(first),components,index,maximum)
}

#[verifier::opaque]
pub open spec fn part1_progression_resolution_levels_owned(
    first:super::Part2OwnedTilePart,components:u16,index:u16,maximum:u8,
) -> Result<u8,crate::DecodeError>
    decreases if index>=components {0nat} else {(components-index) as nat},
{
    if index>=components {Ok(maximum)}
    else {
        match crate::codestream::component_coding_style_result(&first.component_coding_styles,index) {
            Err(error)=>Err(error),
            Ok(style)=>if style.decomposition_levels==u8::MAX || index==u16::MAX {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else {
                let count=(style.decomposition_levels+1) as u8;
                part1_progression_resolution_levels_owned(first,components,(index+1) as u16,if count>maximum {count}else{maximum})
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_progression_selection_check(
    selected:Seq<u8>,available:Seq<u8>,index:usize,
) -> Result<(),crate::DecodeError>
    decreases selected.len()-index as nat,
{
    if index>=selected.len() {Ok(())}
    else if index>=available.len() || selected[index as int]==0 || selected[index as int]>available[index as int] {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
    } else if index==usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
    else {part1_progression_selection_check(selected,available,(index+1) as usize)}
}

pub open spec fn part1_progression_layout(
    parts:Seq<crate::codestream::TilePartPayload<'_>>,grid:Part1PacketGrid,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
) -> Result<(),crate::DecodeError> {
    part1_progression_layout_owned(crate::codestream::tile_parts_owned_view(parts),grid,selection,limits)
}

pub open spec fn part1_progression_layout_owned(
    parts:Seq<super::Part2OwnedTilePart>,grid:Part1PacketGrid,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
) -> Result<(),crate::DecodeError> {
    if parts.len()==0 {Err(ht_reader_error(crate::MalformedKind::InvalidTilePart))}
    else if parts.len() as u64>crate::limits::resource_tile_part_limit(limits) as u64 {
        Err(super::part1_packet_reader_limit(crate::Resource::TileParts,
            crate::limits::resource_tile_part_limit(limits) as u64,parts.len() as u64))
    } else {
        match part1_progression_resolution_levels_owned(parts[0],grid.components,0,0) {
            Err(error)=>Err(error),
            Ok(maximum)=>if parts[0].coding_style.layers!=grid.layers || maximum!=grid.resolutions {
                Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
            } else {
                match selection {
                    None=>Ok(()),
                    Some(selected)=>if selected.len()!=grid.components as nat {
                        Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
                    } else {part1_progression_selection_check(selected,grid.component_resolutions,0)},
                }
            },
        }
    }
}

pub open spec fn part1_progression_payloads(
    parts:Seq<crate::codestream::TilePartPayload<'_>>,s:Part1TilePacketPreparation,maximum_header:u64,
) -> Result<Part1TilePacketPreparation,crate::DecodeError> {
    part1_progression_payloads_owned(crate::codestream::tile_parts_owned_view(parts),s,maximum_header)
}

#[verifier::opaque]
pub open spec fn part1_progression_payloads_owned(
    parts:Seq<super::Part2OwnedTilePart>,s:Part1TilePacketPreparation,maximum_header:u64,
) -> Result<Part1TilePacketPreparation,crate::DecodeError>
    decreases parts.len()-s.index as nat,
{
    if s.index>=parts.len() {Ok(s)}
    else {
        let part=parts[s.index as int];
        if s.index>u8::MAX || part.tile_index!=s.tile_index || part.tile_part_index!=s.index
            || (part.tile_part_count!=0 && part.tile_part_count as nat!=parts.len()) {
            Err(ht_reader_error(crate::MalformedKind::InvalidTilePart))
        } else if s.payload_bytes as nat+(part.data.len() as u64) as nat>u64::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else {
            match super::part1_packed_header_reassembly(
                part.packed_packet_headers,maximum_header) {
                Err(error)=>Err(error),
                Ok(packed)=>if s.packed_payload_bytes as nat+(packed.len() as u64) as nat>u64::MAX {
                    Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                } else if s.packed_payload_bytes as nat+(packed.len() as u64) as nat>maximum_header {
                    Err(super::part1_packet_reader_limit(crate::Resource::PacketHeaderBytes,
                        maximum_header,(s.packed_payload_bytes+packed.len() as u64) as u64))
                } else {
                    let lengths=part.packet_lengths;
                    let present=!matches!(lengths.source,super::Part1PacketLengthSource::None);
                    if present && s.declared_packets as nat+lengths.packet_count as nat>u64::MAX {
                        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                    } else if s.index==usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                    else {part1_progression_payloads_owned(parts,Part1TilePacketPreparation {
                        tile_index:s.tile_index,index:(s.index+1) as usize,
                        payload_bytes:(s.payload_bytes+part.data.len() as u64) as u64,
                        packed_payload_bytes:(s.packed_payload_bytes+packed.len() as u64) as u64,
                        declared_packets:if present {(s.declared_packets+lengths.packet_count) as u64}else{s.declared_packets},
                        all_lengths:s.all_lengths&&present,packed:s.packed.push(packed),
                    },maximum_header)}
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_progression_precinct_indices(
    grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,index:usize,
) -> Result<(),crate::DecodeError>
    decreases precincts.len()-index as nat,
{
    if index>=precincts.len() {Ok(())}
    else {
        let precinct=precincts[index as int];
        match super::part1_packet_grid_precinct_index(grid,precinct.component,precinct.resolution,precinct.precinct) {
            Err(error)=>Err(error),
            Ok(expected)=>if expected!=index {Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader))}
                else if index==usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                else {part1_progression_precinct_indices(grid,precincts,(index+1) as usize)},
        }
    }
}

pub open spec fn part1_progression_precinct_layout(
    grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,
) -> Result<(),crate::DecodeError> {
    match super::part1_packet_grid_total_precincts(grid) {
        Err(error)=>Err(error),
        Ok(count)=>if count as nat>usize::MAX {Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else if precincts.len()!=count as nat {Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader))}
            else {part1_progression_precinct_indices(grid,precincts,0)},
    }
}

pub open spec fn part1_progression_tile_input(
    parts:Seq<crate::codestream::TilePartPayload<'_>>,grid:Part1PacketGrid,
    precincts:Seq<Part1PacketPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
) -> Result<Part1TilePacketPreparation,crate::DecodeError> {
    part1_progression_tile_input_owned(crate::codestream::tile_parts_owned_view(parts),grid,precincts,selection,limits)
}

pub open spec fn part1_progression_tile_input_owned(
    parts:Seq<super::Part2OwnedTilePart>,grid:Part1PacketGrid,
    precincts:Seq<Part1PacketPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
) -> Result<Part1TilePacketPreparation,crate::DecodeError> {
    match part1_progression_layout_owned(parts,grid,selection,limits) {
        Err(error)=>Err(error),
        Ok(())=>match part1_progression_payloads_owned(parts,Part1TilePacketPreparation {
            tile_index:parts[0].tile_index,index:0,payload_bytes:0,packed_payload_bytes:0,
            declared_packets:0,all_lengths:true,packed:Seq::empty(),
        },crate::limits::resource_packet_header_byte_limit(limits)) {
            Err(error)=>Err(error),
            Ok(input)=>if input.all_lengths && input.declared_packets>grid.packet_count {
                Err(ht_reader_error(crate::MalformedKind::InvalidPacketLength))
            } else {match part1_progression_precinct_layout(grid,precincts) {
                Err(error)=>Err(error),Ok(())=>Ok(input),
            }},
        },
    }
}

}
