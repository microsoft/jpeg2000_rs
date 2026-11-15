use super::errors::{
    invalid_packet_header, packet_arithmetic_overflow, packet_reader_error, packet_reader_limit,
};
use super::precinct::decode_precinct_packet;
use super::progression::progression_packet_iterator_new;
use super::{
    CodeBlockPacketContext, DecodeError, MalformedKind, PacketBodyDecode, PacketCoordinate,
    PacketGrid, PacketPrecinctDecoder, ProgressionTileParameters, ProgressionTilePreparation,
    ProgressionTileProgress, Resource, ResourceLimits, TilePacketDecode, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    packet_grid_view, packet_precinct_vector_view, packet_precinct_view, packet_selection_view,
    progression_tile_execution_view, progression_tile_parameters_view,
    progression_tile_preparation_outcome, progression_tile_preparation_view,
    progression_tile_progress_outcome, progression_tile_progress_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,packet_precinct_vector_view(final(precincts)))==crate::specs::part1_progression_tile_decode(
        tile_parts@,packet_grid_view(grid),packet_precinct_vector_view(old(precincts)),None,limits),
))]
pub fn decode_progression_tile_packets(
    tile_parts: &[TilePartPayload<'_>],
    grid: &PacketGrid,
    precincts: &mut [PacketPrecinctDecoder],
    limits: &ResourceLimits,
) -> Result<TilePacketDecode, DecodeError> {
    decode_progression_tile_packets_selected(tile_parts, grid, precincts, None, limits)
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures result==crate::specs::part1_progression_resolution_levels(first,components,0,0),
))]
fn progression_resolution_levels(
    first: &TilePartPayload<'_>,
    components: u16,
) -> Result<u8, DecodeError> {
    let mut maximum = 0_u8;
    let mut component = 0_u16;
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_resolution_levels);reveal(crate::specs::part1_progression_resolution_levels_owned);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant component<=components,
            crate::specs::part1_progression_resolution_levels(first,components,0,0)
                ==crate::specs::part1_progression_resolution_levels(first,components,component,maximum),
        decreases components-component,
    ))]
    while component < components {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_progression_resolution_levels);reveal(crate::specs::part1_progression_resolution_levels_owned);}
        let style = first.component_coding_styles.style(component)?;
        let levels = match style.decomposition_levels.checked_add(1) {
            Some(levels) => levels,
            None => return Err(packet_arithmetic_overflow()),
        };
        maximum = maximum.max(levels);
        component = match component.checked_add(1) {
            Some(component) => component,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_resolution_levels);reveal(crate::specs::part1_progression_resolution_levels_owned);}
    Ok(maximum)
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures result==crate::specs::part1_progression_selection_check(counts@,available@,0),
))]
fn validate_progression_selection(counts: &[u8], available: &[u8]) -> Result<(), DecodeError> {
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_selection_check);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant index<=counts@.len(),
            crate::specs::part1_progression_selection_check(counts@,available@,0)
                ==crate::specs::part1_progression_selection_check(counts@,available@,index),
        decreases counts@.len()-index,
    ))]
    while index < counts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_progression_selection_check);}
        let count = match counts.get(index) {
            Some(count) => *count,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
        };
        let maximum = match available.get(index) {
            Some(count) => *count,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
        };
        if count == 0 || count > maximum {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }
        index = match index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_selection_check);}
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures result==crate::specs::part1_progression_layout(tile_parts@,packet_grid_view(grid),packet_selection_view(selection),limits),
        result.is_ok() ==> tile_parts@.len()>0,
))]
fn validate_progression_layout(
    tile_parts: &[TilePartPayload<'_>],
    grid: &PacketGrid,
    selection: Option<&[u8]>,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_layout);}
    if tile_parts.is_empty() {
        return Err(packet_reader_error(0, MalformedKind::InvalidTilePart));
    }
    if tile_parts.len() as u64 > u64::from(limits.maximum_tile_parts()) {
        return Err(packet_reader_limit(
            Resource::TileParts,
            u64::from(limits.maximum_tile_parts()),
            tile_parts.len() as u64,
        ));
    }
    let first = match tile_parts.first() {
        Some(first) => first,
        None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
    };
    let maximum = progression_resolution_levels(first, grid.components)?;
    if first.coding_style.layers != grid.layers || maximum != grid.resolutions {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }
    if let Some(counts) = selection {
        if counts.len() != usize::from(grid.components) {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }
        validate_progression_selection(counts, &grid.component_resolutions)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures progression_tile_preparation_outcome(result)==crate::specs::part1_progression_payloads(
        tile_parts@,crate::specs::Part1TilePacketPreparation {
            tile_index,index:0,payload_bytes:0,packed_payload_bytes:0,declared_packets:0,all_lengths:true,packed:Seq::empty(),
        },crate::limits::resource_packet_header_byte_limit(limits)),
))]
fn prepare_progression_payloads(
    tile_parts: &[TilePartPayload<'_>],
    tile_index: u16,
    limits: &ResourceLimits,
) -> Result<ProgressionTilePreparation, DecodeError> {
    let mut input = ProgressionTilePreparation {
        tile_index,
        index: 0,
        payload_bytes: 0,
        packed_payload_bytes: 0,
        declared_packets: 0,
        all_lengths: true,
        packed: Vec::with_capacity(tile_parts.len()),
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(input.packed@.map_values(|bytes:Vec<u8>|bytes@) =~= Seq::<Seq<u8>>::empty());
        reveal(crate::specs::part1_progression_payloads);
        reveal(crate::specs::part1_progression_payloads_owned);
    }
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant input.index<=tile_parts@.len(),
            input.tile_index==tile_index,
            crate::specs::part1_progression_payloads(tile_parts@,crate::specs::Part1TilePacketPreparation {
                tile_index,index:0,payload_bytes:0,packed_payload_bytes:0,declared_packets:0,all_lengths:true,packed:Seq::empty(),
            },crate::limits::resource_packet_header_byte_limit(limits))
            ==crate::specs::part1_progression_payloads(tile_parts@,progression_tile_preparation_view(&input),
                crate::limits::resource_packet_header_byte_limit(limits)),
        decreases tile_parts@.len()-input.index,
    ))]
    while input.index < tile_parts.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost prior=progression_tile_preparation_view(&input);}
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_progression_payloads);reveal(crate::specs::part1_progression_payloads_owned);}
        let part = match tile_parts.get(input.index) {
            Some(part) => part,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
        };
        let expected = match u8::try_from(input.index) {
            Ok(index) => index,
            Err(_) => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
        };
        if part.tile_index != input.tile_index
            || part.tile_part_index != expected
            || (part.tile_part_count != 0 && usize::from(part.tile_part_count) != tile_parts.len())
        {
            return Err(packet_reader_error(0, MalformedKind::InvalidTilePart));
        }
        input.payload_bytes = match input.payload_bytes.checked_add(part.data.len() as u64) {
            Some(total) => total,
            None => return Err(packet_arithmetic_overflow()),
        };
        let packed = part.packed_packet_headers.reassemble(limits)?;
        input.packed_payload_bytes =
            match input.packed_payload_bytes.checked_add(packed.len() as u64) {
                Some(total) => total,
                None => return Err(packet_arithmetic_overflow()),
            };
        if input.packed_payload_bytes > limits.maximum_packet_header_bytes() {
            return Err(packet_reader_limit(
                Resource::PacketHeaderBytes,
                limits.maximum_packet_header_bytes(),
                input.packed_payload_bytes,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost prior_packed=input.packed@.map_values(|bytes:Vec<u8>|bytes@);
            let ghost packed_bytes=packed@;
        }
        input.packed.push(packed);
        #[cfg(verus_keep_ghost)]
        proof! {assert(input.packed@.map_values(|bytes:Vec<u8>|bytes@) =~= prior_packed.push(packed_bytes));}
        if part.packet_lengths.is_present() {
            input.declared_packets = match input
                .declared_packets
                .checked_add(part.packet_lengths.packet_count())
            {
                Some(total) => total,
                None => return Err(packet_arithmetic_overflow()),
            };
        } else {
            input.all_lengths = false;
        }
        input.index = match input.index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_payloads);reveal(crate::specs::part1_progression_payloads_owned);}
    Ok(input)
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures result==crate::specs::part1_progression_precinct_layout(packet_grid_view(grid),packet_precinct_vector_view(precincts)),
))]
fn validate_progression_precinct_layout(
    grid: &PacketGrid,
    precincts: &[PacketPrecinctDecoder],
) -> Result<(), DecodeError> {
    let count = match usize::try_from(grid.total_precinct_count()?) {
        Ok(count) => count,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    if precincts.len() != count {
        return Err(invalid_packet_header());
    }
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_precinct_indices);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant index<=precincts@.len(),
            crate::specs::part1_progression_precinct_layout(packet_grid_view(grid),packet_precinct_vector_view(precincts))
                ==crate::specs::part1_progression_precinct_indices(packet_grid_view(grid),packet_precinct_vector_view(precincts),index),
        decreases precincts@.len()-index,
    ))]
    while index < precincts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_progression_precinct_indices);}
        let precinct = match precincts.get(index) {
            Some(precinct) => precinct,
            None => return Err(invalid_packet_header()),
        };
        let expected =
            grid.precinct_index(precinct.component, precinct.resolution, precinct.precinct)?;
        if expected != index {
            return Err(invalid_packet_header());
        }
        index = match index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_progression_precinct_indices);}
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures progression_tile_preparation_outcome(result)==crate::specs::part1_progression_tile_input(
        tile_parts@,packet_grid_view(grid),packet_precinct_vector_view(precincts),packet_selection_view(selection),limits),
        result.is_ok() ==> tile_parts@.len()>0,
))]
pub(super) fn prepare_progression_tile_input(
    tile_parts: &[TilePartPayload<'_>],
    grid: &PacketGrid,
    precincts: &[PacketPrecinctDecoder],
    selection: Option<&[u8]>,
    limits: &ResourceLimits,
) -> Result<ProgressionTilePreparation, DecodeError> {
    validate_progression_layout(tile_parts, grid, selection, limits)?;
    let first = match tile_parts.first() {
        Some(first) => first,
        None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
    };
    let input = prepare_progression_payloads(tile_parts, first.tile_index, limits)?;
    if input.all_lengths && input.declared_packets > grid.packet_count {
        return Err(packet_reader_error(0, MalformedKind::InvalidPacketLength));
    }
    validate_progression_precinct_layout(grid, precincts)?;
    Ok(input)
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures progression_tile_progress_outcome(result)==crate::specs::part1_tile_progress_initial(progression_tile_parameters_view(params)),
))]
pub(super) fn progression_tile_progress_new<'a, 'data>(
    params: &ProgressionTileParameters<'a, 'data>,
) -> Result<ProgressionTileProgress<'a>, DecodeError> {
    let first = match params.tile_parts.first() {
        Some(first) => first,
        None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
    };
    let iterator = progression_packet_iterator_new(
        params.grid,
        first.coding_style.progression_order,
        &first.progression_changes,
        params.limits,
    )?;
    let length_iterator = first.packet_lengths.iter();
    let seen_length = match usize::try_from(params.grid.packet_count) {
        Ok(length) => length,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    let seen = vec![false; seen_length];
    #[cfg(verus_keep_ghost)]
    proof! {assert(seen@ =~= Seq::new(params.grid.packet_count as nat,|i:int|false));}
    Ok(ProgressionTileProgress {
        iterator,
        length_iterator,
        current_tile_part: 0,
        length_tile_part: 0,
        offset: 0,
        packed_offset: 0,
        packets: 0,
        present_packets: 0,
        contributions: 0,
        segments: 0,
        passes: 0,
        packet_header_bytes: 0,
        packet_body_bytes: 0,
        seen,
        remaining_packets: params.limits.maximum_work_units(),
    })
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,progression_tile_progress_view(final(p)))==crate::specs::part1_tile_boundary(
        progression_tile_parameters_view(params),progression_tile_progress_view(old(p))),
))]
fn advance_progression_tile_part<'a, 'data>(
    params: &ProgressionTileParameters<'a, 'data>,
    p: &mut ProgressionTileProgress<'a>,
) -> Result<(bool, bool), DecodeError> {
    let previous = p.current_tile_part;
    scan_progression_tile_boundary(params, p)?;
    if p.current_tile_part != previous {
        let Some(next) = params.tile_parts.get(p.current_tile_part) else {
            return Ok((true, false));
        };
        p.iterator = progression_packet_iterator_new(
            params.grid,
            next.coding_style.progression_order,
            &next.progression_changes,
            params.limits,
        )?;
        Ok((true, true))
    } else {
        Ok((false, true))
    }
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,progression_tile_progress_view(final(p)))==crate::specs::part1_tile_boundary_scan(
        progression_tile_parameters_view(params),progression_tile_progress_view(old(p))),
        progression_tile_progress_view(final(p))==crate::specs::part1_tile_boundary_frame(
            progression_tile_progress_view(old(p)),progression_tile_progress_view(final(p))),
))]
fn scan_progression_tile_boundary<'a, 'data>(
    params: &ProgressionTileParameters<'a, 'data>,
    p: &mut ProgressionTileProgress<'a>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost initial=progression_tile_progress_view(p);}
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_tile_boundary_scan);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant
            progression_tile_progress_view(p)==crate::specs::part1_tile_boundary_frame(
                progression_tile_progress_view(old(p)),progression_tile_progress_view(p)),
            crate::specs::part1_tile_boundary_scan(progression_tile_parameters_view(params),progression_tile_progress_view(old(p)))
                ==crate::specs::part1_tile_boundary_scan(progression_tile_parameters_view(params),progression_tile_progress_view(p)),
        decreases params.tile_parts@.len()-p.current_tile_part,
    ))]
    while p.current_tile_part < params.tile_parts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_tile_boundary_scan);}
        let part = match params.tile_parts.get(p.current_tile_part) {
            Some(part) => part,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
        };
        let packed = match params.input.packed.get(p.current_tile_part) {
            Some(packed) => packed,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
        };
        if p.offset < part.data.len() || p.packed_offset < packed.len() {
            return Ok(());
        }
        if p.offset != part.data.len() || p.packed_offset != packed.len() {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
        if part.packet_lengths.is_present()
            && p.length_tile_part == p.current_tile_part
            && p.length_iterator.next_length()?.is_some()
        {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::InvalidPacketLength,
            ));
        }
        p.current_tile_part = match p.current_tile_part.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
        p.offset = 0;
        p.packed_offset = 0;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_tile_boundary_scan);
        assert((Ok(()),progression_tile_progress_view(p))==
            crate::specs::part1_tile_boundary_scan(progression_tile_parameters_view(params),initial));
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result, final(contexts)@) == crate::specs::part1_packet_context_layers(old(contexts)@, layer),
        result==Ok(()),
        final(contexts)@==old(contexts)@.map_values(|context:CodeBlockPacketContext|
            crate::specs::part1_packet_context_layer(context,layer)),
))]
pub(super) fn set_progression_context_layer(
    contexts: &mut [CodeBlockPacketContext],
    layer: u16,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost initial=contexts@;}
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant index<=contexts@.len(),contexts@.len()==initial.len(),
            forall|i:int|0<=i<contexts@.len() ==> contexts@[i]==if i<index {
                crate::specs::part1_packet_context_layer(initial[i],layer)
            }else{initial[i]},
        decreases contexts@.len()-index,
    ))]
    while index < contexts.len() {
        {
            let context = match contexts.get_mut(index) {
                Some(context) => context,
                None => return Err(invalid_packet_header()),
            };
            context.layer = layer;
        }
        index = match index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {assert(contexts@ =~= initial.map_values(|context:CodeBlockPacketContext|crate::specs::part1_packet_context_layer(context,layer)));}
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,packet_precinct_view(final(precinct)))==crate::specs::part1_tile_precinct_packet(
        progression_tile_parameters_view(params),*part,progression_tile_progress_view(p),coordinate,expected,
        packet_precinct_view(old(precinct))),
))]
fn decode_progression_precinct_packet(
    params: &ProgressionTileParameters<'_, '_>,
    part: &TilePartPayload<'_>,
    p: &ProgressionTileProgress<'_>,
    coordinate: PacketCoordinate,
    expected: Option<u32>,
    precinct: &mut PacketPrecinctDecoder,
) -> Result<(PacketBodyDecode, usize, usize), DecodeError> {
    set_progression_context_layer(&mut precinct.contexts, coordinate.layer)?;
    let packed = match params.input.packed.get(p.current_tile_part) {
        Some(packed) => packed,
        None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
    };
    let decode = match params.selection {
        Some(counts) => {
            coordinate.resolution
                < *match counts.get(usize::from(coordinate.component)) {
                    Some(count) => count,
                    None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
                }
        }
        None => true,
    };
    let word = p.packets;
    #[cfg(verus_keep_ghost)]
    proof! {assert(word & 65535u64 <= 65535u64) by(bit_vector);}
    let sequence = match u16::try_from(word & u64::from(u16::MAX)) {
        Ok(sequence) => sequence,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    decode_precinct_packet(
        part,
        p.offset,
        packed,
        p.packed_offset,
        expected,
        sequence,
        precinct,
        decode,
        params.limits,
    )
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,progression_tile_execution_view(final(precincts),final(p)))==crate::specs::part1_tile_packet(
        progression_tile_parameters_view(params),progression_tile_execution_view(old(precincts),old(p)),coordinate),
))]
fn execute_progression_packet<'a, 'data>(
    params: &ProgressionTileParameters<'a, 'data>,
    precincts: &mut [PacketPrecinctDecoder],
    p: &mut ProgressionTileProgress<'a>,
    coordinate: PacketCoordinate,
) -> Result<(), DecodeError> {
    let part = match params.tile_parts.get(p.current_tile_part) {
        Some(part) => part,
        None => {
            return Err(DecodeError::MalformedInput {
                offset: params.input.payload_bytes,
                kind: MalformedKind::Truncated,
            });
        }
    };
    let slot = progression_packet_slot(params.grid, coordinate);
    let duplicate = match slot {
        Ok((_, seen)) => match p.seen.get(seen) {
            Some(seen) => *seen,
            None => false,
        },
        Err(_) => false,
    };
    // Restarted iterators must not consume physical lengths for prior packets.
    // Invalid new slots still retain metadata-first error ordering below.
    if duplicate {
        return Ok(());
    }
    if p.length_tile_part != p.current_tile_part {
        p.length_iterator = part.packet_lengths.iter();
        p.length_tile_part = p.current_tile_part;
    }
    let expected = if part.packet_lengths.is_present() {
        Some(match p.length_iterator.next_length()? {
            Some(length) => length,
            None => {
                return Err(packet_reader_error(
                    p.offset,
                    MalformedKind::InvalidPacketLength,
                ));
            }
        })
    } else {
        None
    };
    let (index, seen_index) = slot?;
    let seen = match p.seen.get(seen_index) {
        Some(seen) => *seen,
        None => {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::InvalidPacketHeader,
            ));
        }
    };
    if !crate::refinement::progression_emit_allowed(seen) {
        return Ok(());
    }
    if index >= precincts.len() {
        return Err(packet_reader_error(
            p.offset,
            MalformedKind::InvalidPacketHeader,
        ));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost prior_native=precincts@;
        let ghost prior=packet_precinct_vector_view(precincts);
        let ghost packet_expected=crate::specs::part1_tile_precinct_packet(
            progression_tile_parameters_view(params),*part,progression_tile_progress_view(p),coordinate,expected,prior[index as int]);
    }
    let result = {
        let precinct = &mut precincts[index];
        decode_progression_precinct_packet(params, part, p, coordinate, expected, precinct)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:int|0<=i<precincts@.len() && i!=index as int implies precincts@[i]==prior_native[i] by {}
        assert(packet_precinct_vector_view(precincts) =~= prior.update(index as int,packet_expected.1));
        assert(result==packet_expected.0);
    }
    let (decoded, tile_bytes, packed_bytes) = result?;
    account_progression_packet(p, decoded, tile_bytes, packed_bytes, expected, seen_index)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_tile_packet_slot(packet_grid_view(grid), coordinate),
))]
fn progression_packet_slot(
    grid: &PacketGrid,
    coordinate: PacketCoordinate,
) -> Result<(usize, usize), DecodeError> {
    let index = grid.precinct_index(
        coordinate.component,
        coordinate.resolution,
        coordinate.precinct,
    )?;
    let product = match index.checked_mul(usize::from(grid.layers)) {
        Some(product) => product,
        None => return Err(packet_arithmetic_overflow()),
    };
    let seen = match product.checked_add(usize::from(coordinate.layer)) {
        Some(seen) => seen,
        None => return Err(packet_arithmetic_overflow()),
    };
    Ok((index, seen))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, progression_tile_progress_view(final(p))) == crate::specs::part1_tile_omit_packet(
        progression_tile_parameters_view(params), progression_tile_progress_view(old(p)),
        coordinate, precinct_count),
))]
fn omit_progression_packet(
    params: &ProgressionTileParameters<'_, '_>,
    p: &mut ProgressionTileProgress<'_>,
    coordinate: PacketCoordinate,
    precinct_count: usize,
) -> Result<(), DecodeError> {
    let (index, seen) = progression_packet_slot(params.grid, coordinate)?;
    if index >= precinct_count || seen >= p.seen.len() {
        return Err(packet_reader_error(
            p.offset,
            MalformedKind::InvalidPacketHeader,
        ));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost previous = p.seen@; }
    p.seen[seen] = true;
    #[cfg(verus_keep_ghost)]
    proof! { assert(p.seen@ =~= previous.update(seen as int, true)); }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_tile_all_seen(seen@),
))]
fn all_progression_packets_seen(seen: &[bool]) -> bool {
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= seen@.len(),
            forall |i: int| 0 <= i < index ==> seen@[i],
        decreases seen@.len() - index,
    ))]
    while index < seen.len() {
        if !seen[index] {
            return false;
        }
        index += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,progression_tile_progress_view(final(p)))==crate::specs::part1_tile_account(
        progression_tile_progress_view(old(p)),decoded,tile_bytes,packed_bytes,expected,seen_index),
))]
pub(super) fn account_progression_packet(
    p: &mut ProgressionTileProgress<'_>,
    decoded: PacketBodyDecode,
    tile_bytes: usize,
    packed_bytes: usize,
    expected: Option<u32>,
    seen_index: usize,
) -> Result<(), DecodeError> {
    if seen_index >= p.seen.len() {
        return Err(packet_reader_error(
            p.offset,
            MalformedKind::InvalidPacketHeader,
        ));
    }
    if decoded.bytes_consumed == 0 {
        return Err(packet_reader_error(
            p.offset,
            MalformedKind::InvalidPacketHeader,
        ));
    }
    match expected {
        Some(expected) if decoded.bytes_consumed != expected => {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::InvalidPacketLength,
            ));
        }
        _ => {}
    }
    p.offset = match p.offset.checked_add(tile_bytes) {
        Some(offset) => offset,
        None => {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    p.packed_offset = match p.packed_offset.checked_add(packed_bytes) {
        Some(offset) => offset,
        None => {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::ArithmeticOverflow,
            ));
        }
    };
    p.packets = match p.packets.checked_add(1) {
        Some(total) => total,
        None => return Err(packet_arithmetic_overflow()),
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost prior_seen=p.seen@;}
    p.seen[seen_index] = true;
    #[cfg(verus_keep_ghost)]
    proof! {assert(p.seen@ =~= prior_seen.update(seen_index as int,true));}
    let present = if decoded.present { 1_u64 } else { 0_u64 };
    p.present_packets = match p.present_packets.checked_add(present) {
        Some(total) => total,
        None => return Err(packet_arithmetic_overflow()),
    };
    p.contributions = match p
        .contributions
        .checked_add(u64::from(decoded.contributions))
    {
        Some(total) => total,
        None => return Err(packet_arithmetic_overflow()),
    };
    p.segments = match p.segments.checked_add(u64::from(decoded.segments)) {
        Some(total) => total,
        None => return Err(packet_arithmetic_overflow()),
    };
    p.passes = match p.passes.checked_add(u64::from(decoded.passes)) {
        Some(total) => total,
        None => return Err(packet_arithmetic_overflow()),
    };
    p.packet_header_bytes = match p
        .packet_header_bytes
        .checked_add(u64::from(decoded.header_bytes))
    {
        Some(total) => total,
        None => return Err(packet_arithmetic_overflow()),
    };
    p.packet_body_bytes = match p
        .packet_body_bytes
        .checked_add(u64::from(decoded.body_bytes))
    {
        Some(total) => total,
        None => return Err(packet_arithmetic_overflow()),
    };
    Ok(())
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,progression_tile_progress_view(final(p)))==crate::specs::part1_tile_finish(
        progression_tile_parameters_view(params),progression_tile_progress_view(old(p))),
))]
fn finish_progression_tile_packets(
    params: &ProgressionTileParameters<'_, '_>,
    p: &mut ProgressionTileProgress<'_>,
) -> Result<TilePacketDecode, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_tile_finish_scan);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant crate::specs::part1_tile_finish_scan(progression_tile_parameters_view(params),progression_tile_progress_view(old(p)))
            ==crate::specs::part1_tile_finish_scan(progression_tile_parameters_view(params),progression_tile_progress_view(p)),
        decreases params.tile_parts@.len()-p.current_tile_part,
    ))]
    while p.current_tile_part < params.tile_parts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_tile_finish_scan);}
        let part = match params.tile_parts.get(p.current_tile_part) {
            Some(part) => part,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
        };
        let packed = match params.input.packed.get(p.current_tile_part) {
            Some(packed) => packed,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidTilePart)),
        };
        if p.offset != part.data.len() || p.packed_offset != packed.len() {
            return Err(packet_reader_error(p.offset, MalformedKind::TrailingData));
        }
        if part.packet_lengths.is_present()
            && p.length_tile_part == p.current_tile_part
            && p.length_iterator.next_length()?.is_some()
        {
            return Err(packet_reader_error(
                p.offset,
                MalformedKind::InvalidPacketLength,
            ));
        }
        p.current_tile_part = match p.current_tile_part.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
        p.offset = 0;
        p.packed_offset = 0;
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_tile_finish_scan);}
    if p.packets != params.grid.packet_count
        && (p.packets > params.grid.packet_count
            || p.packets == 0
            || p.seen.len() as u128 != u128::from(params.grid.packet_count)
            || !all_progression_packets_seen(&p.seen))
    {
        return Err(DecodeError::MalformedInput {
            offset: params.input.payload_bytes,
            kind: MalformedKind::Truncated,
        });
    }
    if params.input.all_lengths && p.packets != params.input.declared_packets {
        return Err(packet_reader_error(0, MalformedKind::InvalidPacketLength));
    }
    let tile_parts = match u32::try_from(params.tile_parts.len()) {
        Ok(count) => count,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    Ok(TilePacketDecode {
        tile_index: params.input.tile_index,
        tile_parts,
        packets: p.packets,
        present_packets: p.present_packets,
        contributions: p.contributions,
        segments: p.segments,
        passes: p.passes,
        packet_header_bytes: p.packet_header_bytes,
        packet_body_bytes: p.packet_body_bytes,
        payload_bytes: params.input.payload_bytes,
    })
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,packet_precinct_vector_view(final(precincts)))==crate::specs::part1_progression_tile_decode(
        tile_parts@,packet_grid_view(grid),packet_precinct_vector_view(old(precincts)),packet_selection_view(maximum_resolution_counts),limits),
))]
pub(crate) fn decode_progression_tile_packets_selected(
    tile_parts: &[TilePartPayload<'_>],
    grid: &PacketGrid,
    precincts: &mut [PacketPrecinctDecoder],
    maximum_resolution_counts: Option<&[u8]>,
    limits: &ResourceLimits,
) -> Result<TilePacketDecode, DecodeError> {
    let input = prepare_progression_tile_input(
        tile_parts,
        grid,
        precincts,
        maximum_resolution_counts,
        limits,
    )?;
    let params = ProgressionTileParameters {
        tile_parts,
        grid,
        input: &input,
        selection: maximum_resolution_counts,
        limits,
    };
    let mut progress = progression_tile_progress_new(&params)?;
    run_progression_tile_packets(&params, precincts, &mut progress)?;
    finish_progression_tile_packets(&params, &mut progress)
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,progression_tile_execution_view(final(precincts),final(p)))==crate::specs::part1_tile_run(
        progression_tile_parameters_view(params),progression_tile_execution_view(old(precincts),old(p))),
))]
pub(super) fn run_progression_tile_packets<'a, 'data>(
    params: &ProgressionTileParameters<'a, 'data>,
    precincts: &mut [PacketPrecinctDecoder],
    p: &mut ProgressionTileProgress<'a>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_tile_run);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant crate::specs::part1_tile_run(progression_tile_parameters_view(params),
            progression_tile_execution_view(old(precincts),old(p)))
            ==crate::specs::part1_tile_run(progression_tile_parameters_view(params),progression_tile_execution_view(precincts,p)),
        decreases p.remaining_packets,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_tile_run);}
        let coordinate = match p.iterator.next_packet()? {
            Some(coordinate) => coordinate,
            None => return Ok(()),
        };
        if p.remaining_packets == 0 {
            return Err(packet_reader_error(
                0,
                MalformedKind::InvalidProgressionOrderChange,
            ));
        }
        p.remaining_packets -= 1;
        if p.current_tile_part == params.tile_parts.len() {
            omit_progression_packet(params, p, coordinate, precincts.len())?;
            continue;
        }
        let (changed, more) = advance_progression_tile_part(params, p)?;
        if changed {
            if more {
                continue;
            } else {
                omit_progression_packet(params, p, coordinate, precincts.len())?;
                continue;
            }
        }
        execute_progression_packet(params, precincts, p, coordinate)?;
    }
}
