use crate::{DecodeError, DecodeOptions, MalformedKind, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
pub(crate) struct CountShape {
    pub(crate) first: usize,
    pub(crate) declared: u8,
    pub(crate) parts: usize,
    pub(crate) max_tile: usize,
}

pub(crate) struct PdfCountRepair {
    pub(crate) bytes: Vec<u8>,
    pub(crate) fields: u32,
    pub(crate) work_units: u64,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn count_fields_outcome(result: Result<Vec<usize>, DecodeError>)
        -> Result<Seq<usize>, DecodeError> {
        match result { Err(error) => Err(error), Ok(fields) => Ok(fields@) }
    }
    pub(crate) open spec fn count_repair_outcome(result: Result<PdfCountRepair, DecodeError>)
        -> Result<crate::specs::Part2PdfCountRepair, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) => Ok((value.bytes@, value.fields, value.work_units)) }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (pos as nat + 2 <= stream.len()
        && stream@[pos as int] == 255 && stream@[pos as int + 1] == code),
))]
fn marker_at(stream: &[u8], pos: usize, code: u8) -> bool {
    if pos >= stream.len() || stream.len() - pos < 2 {
        return false;
    }
    stream[pos] == 255 && stream[pos + 1] == code
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires stream.len() >= 2,
    ensures result == crate::specs::part2_count_header_start(stream@, 2, error),
        result.is_ok() ==> result.get_Ok_0() <= stream.len(),
))]
fn first_sot(stream: &[u8], error: DecodeError) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part2_count_header_start(stream@, 2, error);
    }
    let mut pos = 2_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant goal == crate::specs::part2_count_header_start(stream@, pos as nat, error),
            goal == crate::specs::part2_count_header_start(stream@, 2, error),
            2 <= pos <= stream.len(),
        decreases stream.len() as int - pos,
    ))]
    while !marker_at(stream, pos, 144) {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_count_header_start, 1); }
        let end = pos.checked_add(4).ok_or(error)?;
        let header = stream.get(pos..end).ok_or(error)?;
        if header[0] != 255 || header[1] < 0x50 || header[1] > 0x8f {
            return Err(error);
        }
        let length = usize::from(crate::codestream::read_u16([header[2], header[3]]));
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(length as nat == crate::specs::part1_marker_value(stream@[pos as int + 2], stream@[pos as int + 3]) as nat);
        }
        if length < 2 {
            return Err(error);
        }
        let payload = pos.checked_add(2).ok_or(error)?;
        pos = payload.checked_add(length).ok_or(error)?;
        if pos > stream.len() {
            return Err(error);
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_count_header_start, 1); }
    Ok(pos)
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_count_shape(stream@, error_offset, limits, error),
        result.is_ok() ==> 0 < result.get_Ok_0().declared < 255
            && 0 < result.get_Ok_0().parts
            && result.get_Ok_0().first <= stream.len()
            && result.get_Ok_0().max_tile <= u16::MAX
            && result.get_Ok_0().parts <= crate::limits::resource_tile_part_limit(limits),
))]
fn scan_shape(
    stream: &[u8],
    error_offset: u64,
    limits: &ResourceLimits,
    error: DecodeError,
) -> Result<CountShape, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_count_shape); }
    if !marker_at(stream, 0, 79) {
        return Err(error);
    }
    let mut pos = first_sot(stream, error)?;
    let first = pos;
    let mut declared = None;
    let mut parts = 0_usize;
    let mut max_tile = 0_usize;
    let mut matched_error = false;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part2_count_shape_walk(stream@, error_offset, limits, error,
            first as nat, first, None, 0, 0, false);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant pos <= stream.len(), first <= pos,
            parts <= crate::limits::resource_tile_part_limit(limits),
            max_tile <= u16::MAX,
            declared.is_some() == (parts > 0),
            declared.is_some() ==> 0 < declared.get_Some_0() < 255,
            matched_error ==> parts > 0,
            goal == crate::specs::part2_count_shape(stream@, error_offset, limits, error),
            goal == crate::specs::part2_count_shape_walk(stream@, error_offset, limits, error,
                pos as nat, first, declared, parts as nat, max_tile as nat, matched_error),
        decreases stream.len() - pos,
    ))]
    while stream.len() - pos != 2 || !marker_at(stream, pos, 217) {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_count_shape_walk, 1); }
        let end = pos.checked_add(12).ok_or(error)?;
        let part = stream.get(pos..end).ok_or(error)?;
        if part[0] != 255
            || part[1] != 144
            || part[2] != 0
            || part[3] != 10
            || part[11] == 0
            || part[11] == 255
        {
            return Err(error);
        }
        match declared {
            None => declared = Some(part[11]),
            Some(value) if value != part[11] => return Err(error),
            Some(_) => {}
        }
        if parts as u64 >= u64::from(limits.maximum_tile_parts()) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TileParts,
                limit: u64::from(limits.maximum_tile_parts()),
                actual: parts as u64 + 1,
            });
        }
        let tile = usize::from(crate::codestream::read_u16([part[4], part[5]]));
        #[cfg(verus_keep_ghost)]
        proof! { assert(tile as nat == crate::specs::part2_count_tile(stream@, pos as nat)); }
        if tile as u64 >= u64::from(limits.maximum_tiles()) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Tiles,
                limit: u64::from(limits.maximum_tiles()),
                actual: tile as u64 + 1,
            });
        }
        max_tile = max_tile.max(tile);
        matched_error |= part[10] == part[11] && pos as u64 == error_offset;
        let length = crate::codestream::read_u32([part[6], part[7], part[8], part[9]]) as usize;
        #[cfg(verus_keep_ghost)]
        proof! { assert(length as nat == crate::specs::part2_count_part_length(stream@, pos as nat)); }
        if length < 14 {
            return Err(error);
        }
        pos = pos.checked_add(length).ok_or(error)?;
        if pos > stream.len() {
            return Err(error);
        }
        parts = parts.checked_add(1).ok_or(error)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(pos as nat + 2 == stream.len());
        assert(stream@[pos as int] == 255 && stream@[pos as int + 1] == 217);
        reveal_with_fuel(crate::specs::part2_count_shape_walk, 1);
    }
    if !matched_error {
        return Err(error);
    }
    Ok(CountShape {
        first,
        declared: declared.ok_or(error)?,
        parts,
        max_tile,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_count_admit(input_bytes, shape, limits),
))]
fn admit_repair(
    input_bytes: usize,
    shape: CountShape,
    limits: &ResourceLimits,
) -> Result<u64, DecodeError> {
    let overflow = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let table = (shape.max_tile as u64).checked_add(1).ok_or(overflow)?;
    let table_bytes = table.checked_mul(2).ok_or(overflow)?;
    let positions_bytes = (shape.parts as u64).checked_mul(8).ok_or(overflow)?;
    let owners = table_bytes.checked_add(positions_bytes).ok_or(overflow)?;
    let scratch = owners.checked_add(input_bytes as u64).ok_or(overflow)?;
    if scratch > limits.maximum_decoded_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: limits.maximum_decoded_bytes(),
            actual: scratch,
        });
    }
    let passes = (input_bytes as u64).checked_mul(4).ok_or(overflow)?;
    let with_table = passes.checked_add(table).ok_or(overflow)?;
    let work = with_table.checked_add(shape.parts as u64).ok_or(overflow)?;
    if work > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: work,
        });
    }
    Ok(work)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == forall|i:int| 0 <= i < next.len()
        ==> next@[i] == 0 || next@[i] == declared as nat + 1,
))]
fn complete_counts(next: &[u16], declared: u8) -> bool {
    let total = u16::from(declared) + 1;
    let mut tile = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tile <= next.len(),
            total as nat == declared as nat + 1,
            forall|i:int| 0 <= i < tile ==> next@[i] == 0 || next@[i] == total,
        decreases next.len() - tile,
    ))]
    while tile < next.len() {
        if next[tile] != 0 && next[tile] != total {
            return false;
        }
        tile += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 0 < shape.declared < 255, shape.first <= stream.len(),
        shape.max_tile < usize::MAX, shape.parts > 0,
    ensures crate::specs::part2_count_fields_result(stream@, shape, error, count_fields_outcome(result)),
        result.is_ok() ==> result.get_Ok_0().len() == shape.parts,
        count_fields_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            count_fields_outcome(result) == crate::specs::part2_count_fields_value(stream@, shape, error),
))]
fn count_fields(
    stream: &[u8],
    shape: CountShape,
    error: DecodeError,
) -> Result<Vec<usize>, DecodeError> {
    let slots = shape.max_tile.checked_add(1).ok_or(error)?;
    let allocated = crate::allocation::empty_with_capacity(slots);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(_) = allocated { crate::specs::part2_count_fields_refused(stream@, shape, error, 0); }
    }
    let mut next = allocated?;
    next.resize(slots, 0_u16);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:int| 0 <= i < slots implies next@[i] == 0u16 by {
            assert(vstd::pervasive::cloned::<u16>(0u16, next@[i]));
        }
        assert(next@ =~= Seq::new(slots as nat, |_:int| 0u16));
    }
    let allocated = crate::allocation::empty_with_capacity(shape.parts);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(_) = allocated { crate::specs::part2_count_fields_refused(stream@, shape, error, 1); }
    }
    let mut fields = allocated?;
    let mut pos = shape.first;
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_count_fields_normal(stream@, shape, error); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant pos <= stream.len(),
            0 < shape.declared < 255,
            shape.parts > 0,
            shape.max_tile < usize::MAX,
            fields.len() <= shape.parts,
            next.len() == slots,
            slots == shape.max_tile + 1,
            crate::specs::part2_count_fields_result(stream@, shape, error,
                crate::specs::part2_count_fields_value(stream@, shape, error)),
            crate::specs::part2_count_fields_value(stream@, shape, error)
                == crate::specs::part2_count_validate(stream@, shape, error, pos as nat, next@, fields@),
        decreases shape.parts - fields.len(),
    ))]
    while fields.len() < shape.parts {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_count_validate, 1); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_pos = pos;
            let ghost previous_next = next@;
            let ghost previous_fields = fields@;
        }
        let end = pos.checked_add(12).ok_or(error)?;
        let part = stream.get(pos..end).ok_or(error)?;
        if part[0] != 255
            || part[1] != 144
            || part[2] != 0
            || part[3] != 10
            || part[11] != shape.declared
        {
            return Err(error);
        }
        let tile = usize::from(crate::codestream::read_u16([part[4], part[5]]));
        if tile >= next.len() || next[tile] != u16::from(part[10]) || part[10] > shape.declared {
            return Err(error);
        }
        let length = crate::codestream::read_u32([part[6], part[7], part[8], part[9]]) as usize;
        if length < 14 {
            return Err(error);
        }
        let next_pos = pos.checked_add(length).ok_or(error)?;
        if next_pos > stream.len() {
            return Err(error);
        }
        let field = pos.checked_add(11).ok_or(error)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(tile as nat == crate::specs::part2_count_tile(stream@, pos as nat));
            assert(length as nat == crate::specs::part2_count_part_length(stream@, pos as nat));
            assert(previous_next[tile as int] == stream@[pos as int + 10] as nat);
            assert(next_pos as nat == pos as nat + crate::specs::part2_count_part_length(stream@, pos as nat));
            reveal_with_fuel(crate::specs::part2_count_validate, 2);
            crate::specs::part2_count_validate_step(stream@, shape, error, pos as nat, previous_next, previous_fields);
            assert(crate::specs::part2_count_validate(stream@, shape, error, pos as nat, previous_next, previous_fields)
                == crate::specs::part2_count_validate(stream@, shape, error, next_pos as nat,
                    previous_next.update(tile as int, (previous_next[tile as int] + 1) as u16),
                    previous_fields.push(field)));
            assert(crate::specs::part2_count_fields_value(stream@, shape, error)
                == crate::specs::part2_count_validate(stream@, shape, error, next_pos as nat,
                    previous_next.update(tile as int, (previous_next[tile as int] + 1) as u16),
                    previous_fields.push(field)));
        }
        next[tile] += 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(next@ =~= previous_next.update(tile as int, (previous_next[tile as int] + 1) as u16));
        }
        fields.push(field);
        pos = next_pos;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(fields@ =~= previous_fields.push((previous_pos + 11) as usize));
            assert(crate::specs::part2_count_fields_value(stream@, shape, error)
                == crate::specs::part2_count_validate(stream@, shape, error, pos as nat, next@, fields@));
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_count_validate, 1); }
    if stream.len() - pos != 2 || !marker_at(stream, pos, 217) {
        return Err(error);
    }
    if !complete_counts(&next, shape.declared) {
        return Err(error);
    }
    Ok(fields)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires declared < 255,
    ensures crate::specs::part2_count_copy_result(input@, base, positions@, declared, error,
        crate::recovery::repair_outcome(result)),
        result.is_ok() ==> result.get_Ok_0().len() == input.len(),
        crate::recovery::repair_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            crate::recovery::repair_outcome(result) == crate::specs::part2_count_patch(input@, base, positions@, declared, error, 0),
))]
fn patch_copy(
    input: &[u8],
    base: usize,
    positions: &[usize],
    declared: u8,
    error: DecodeError,
) -> Result<Vec<u8>, DecodeError> {
    let copied = crate::allocation::copy_values(input);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(_) = copied { crate::specs::part2_count_copy_refused(input@, base, positions@, declared, error); }
    }
    let mut repaired = copied?;
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_count_copy_normal(input@, base, positions@, declared, error); }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= positions.len(), declared < 255,
            repaired.len() == input.len(),
            crate::specs::part2_count_copy_result(input@, base, positions@, declared, error,
                crate::specs::part2_count_patch(input@, base, positions@, declared, error, 0)),
            crate::specs::part2_count_patch(input@, base, positions@, declared, error, 0)
                == crate::specs::part2_count_patch(repaired@, base, positions@, declared, error, index as nat),
        decreases positions.len() - index,
    ))]
    while index < positions.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_count_patch, 1); }
        let position = base.checked_add(positions[index]).ok_or(error)?;
        *repaired.get_mut(position).ok_or(error)? = declared + 1;
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_count_patch, 1); }
    Ok(repaired)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_count_initial_admit(input_bytes, limits, error),
))]
pub(crate) fn admit_input(
    input_bytes: usize,
    limits: &ResourceLimits,
    error: DecodeError,
) -> Result<u64, DecodeError> {
    let DecodeError::MalformedInput {
        offset,
        kind: MalformedKind::InvalidTilePart,
    } = error
    else {
        return Err(error);
    };
    if input_bytes as u64 > limits.maximum_input_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: limits.maximum_input_bytes(),
            actual: input_bytes as u64,
        });
    }
    if input_bytes as u64 > limits.maximum_decoded_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: limits.maximum_decoded_bytes(),
            actual: input_bytes as u64,
        });
    }
    let initial_work = (input_bytes as u64)
        .checked_mul(4)
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })?;
    if initial_work > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: initial_work,
        });
    }
    Ok(offset)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_count_repair_result(input@, stream@, base,
        crate::options::decode_options_limits(options), error, count_repair_outcome(result)),
        count_repair_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            count_repair_outcome(result) == crate::specs::part2_count_repair_value(input@, stream@, base,
                crate::options::decode_options_limits(options), error),
))]
pub(crate) fn recover_pdf_tile_part_counts(
    input: &[u8],
    stream: &[u8],
    base: usize,
    options: &DecodeOptions,
    error: DecodeError,
) -> Result<PdfCountRepair, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::decoder_layout_errors_known(); }
    let limits = options.limits();
    let admitted = admit_input(input.len(), limits, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = admitted {
            crate::specs::part2_count_repair_preflight_error(input@, stream@, base,
                crate::options::decode_options_limits(options), error, failure);
        }
    }
    let offset = admitted?;
    let end = match base.checked_add(stream.len()) {
        Some(end) if end <= input.len() => end,
        _ => {
            #[cfg(verus_keep_ghost)]
            proof! { crate::specs::part2_count_repair_preflight_error(input@, stream@, base,
            crate::options::decode_options_limits(options), error, error); }
            return Err(error);
        }
    };
    if &input[base..end] != stream {
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part2_count_repair_preflight_error(input@, stream@, base,
        crate::options::decode_options_limits(options), error, error); }
        return Err(error);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(stream@ =~= input@.subrange(base as int, end as int));
        assert(crate::specs::part2_count_source_matches(input@, stream@, base));
    }
    let scanned = scan_shape(stream, offset, limits, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = scanned {
            crate::specs::part2_count_repair_preflight_error(input@, stream@, base,
                crate::options::decode_options_limits(options), error, failure);
        }
    }
    let shape = scanned?;
    let admitted = admit_repair(input.len(), shape, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = admitted {
            crate::specs::part2_count_repair_preflight_error(input@, stream@, base,
                crate::options::decode_options_limits(options), error, failure);
        }
    }
    let work_units = admitted?;
    let counted = count_fields(stream, shape, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = counted {
            crate::specs::part2_count_repair_fields_lift(input@, stream@, base,
                crate::options::decode_options_limits(options), error, offset, shape, work_units,
                count_fields_outcome(counted), Err(failure));
        }
    }
    let positions = counted?;
    let fields = u32::try_from(positions.len()).map_err(|_| error)?;
    let copied = patch_copy(input, base, &positions, shape.declared, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = copied {
            crate::specs::part2_count_repair_copy_lift(input@, stream@, base,
                crate::options::decode_options_limits(options), error, shape, positions@, work_units,
                crate::recovery::repair_outcome(copied), Err(failure));
            crate::specs::part2_count_repair_fields_lift(input@, stream@, base,
                crate::options::decode_options_limits(options), error, offset, shape, work_units,
                Ok(positions@), Err(failure));
        }
    }
    let repaired = copied?;
    let end = base.checked_add(stream.len()).ok_or(error)?;
    let parsed = crate::codestream::parse_layout(&repaired[base..end], limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Ok(layout) = parsed { crate::codestream::decoder_layout_complete_info_matches_raw(&layout); }
        let value = match crate::codestream::complete_layout_outcome(parsed) {
            Err(failure) => Err(failure), Ok(_) => Ok((repaired@, fields, work_units)),
        };
        crate::specs::part2_count_repair_parsed_lift(input@, stream@, base,
            crate::options::decode_options_limits(options), error, positions@, work_units, repaired@,
            crate::codestream::complete_layout_outcome(parsed));
        crate::specs::part2_count_repair_copy_lift(input@, stream@, base,
            crate::options::decode_options_limits(options), error, shape, positions@, work_units,
            Ok(repaired@), value);
        crate::specs::part2_count_repair_fields_lift(input@, stream@, base,
            crate::options::decode_options_limits(options), error, offset, shape, work_units,
            Ok(positions@), value);
    }
    parsed?;
    Ok(PdfCountRepair {
        bytes: repaired,
        fields,
        work_units,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interleaved(parts: &[(u8, u8, u8)]) -> Vec<u8> {
        let mut bytes = vec![255, 79];
        for &(tile, index, declared) in parts {
            bytes.extend_from_slice(&[
                255, 144, 0, 10, 0, tile, 0, 0, 0, 14, index, declared, 255, 147,
            ]);
        }
        bytes.extend_from_slice(&[255, 217]);
        bytes
    }

    #[test]
    fn count_fields_require_complete_ordered_parts_at_the_reported_offset() {
        let limits = ResourceLimits::default();
        let error = DecodeError::MalformedInput {
            offset: 30,
            kind: MalformedKind::InvalidTilePart,
        };
        let bytes = interleaved(&[(0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)]);
        let shape = scan_shape(&bytes, 30, &limits, error).unwrap();
        assert_eq!(
            count_fields(&bytes, shape, error).unwrap(),
            [13, 27, 41, 55]
        );
        assert!(scan_shape(&bytes, 29, &limits, error).is_err());
        assert!(scan_shape(&bytes[..bytes.len() - 1], 30, &limits, error).is_err());
        for parts in [
            [(0, 0, 1), (1, 0, 1), (0, 1, 1), (2, 0, 1)],
            [(0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 2)],
            [(0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 2, 1)],
        ] {
            let input = interleaved(&parts);
            assert_eq!(
                scan_shape(&input, 30, &limits, error)
                    .and_then(|shape| count_fields(&input, shape, error)),
                Err(error),
            );
        }
    }

    #[test]
    fn count_storage_refusals_propagate_and_restore_without_changing_other_bytes() {
        let limits = ResourceLimits::default();
        let error = DecodeError::MalformedInput {
            offset: 30,
            kind: MalformedKind::InvalidTilePart,
        };
        let bytes = interleaved(&[(0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)]);
        let shape = scan_shape(&bytes, 30, &limits, error).unwrap();
        for after in 0..2 {
            assert_eq!(
                crate::allocation::with_refusal(after, || count_fields(&bytes, shape, error)),
                Err(DecodeError::AllocationFailed),
            );
        }
        let fields = count_fields(&bytes, shape, error).unwrap();
        assert_eq!(
            crate::allocation::with_refusal(0, || patch_copy(&bytes, 0, &fields, 1, error)),
            Err(DecodeError::AllocationFailed),
        );
        let repaired = patch_copy(&bytes, 0, &fields, 1, error).unwrap();
        for (index, (&before, &after)) in bytes.iter().zip(&repaired).enumerate() {
            assert_eq!(after, if fields.contains(&index) { 2 } else { before });
        }
        let limited = limits
            .with_maximum_decoded_bytes(bytes.len() as u64)
            .unwrap();
        assert!(matches!(
            admit_repair(bytes.len(), shape, &limited),
            Err(DecodeError::LimitExceeded {
                resource: Resource::DecodedBytes,
                ..
            })
        ));
        let limited = limits
            .with_maximum_work_units(bytes.len() as u64 * 4)
            .unwrap();
        assert!(matches!(
            admit_repair(bytes.len(), shape, &limited),
            Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                ..
            })
        ));
    }
}
