use crate::{jp2, DecodeError, DecodeOptions, MalformedKind, ResourceLimits};

/// Prototype PDF recovery for a complete codestream whose tile-part counts
/// consistently encode the final zero-based index instead of the total.
///
/// Call only after inspection rejects the original stream. This native-only
/// preflight changes only TNsot bytes and requires a successful PDF-compatible
/// inspection of the repaired input. It does not repair entropy or synthesize
/// missing tile parts. Strict decoding and the verified APIs are unchanged.
pub fn recover_pdf_tile_part_counts(
    input: &[u8],
    options: &DecodeOptions,
    error: DecodeError,
) -> Result<Vec<u8>, DecodeError> {
    let DecodeError::MalformedInput { offset, kind: MalformedKind::InvalidTilePart } = error else {
        return Err(error);
    };
    let limits = options.limits();
    let size = input.len() as u64;
    if size > limits.maximum_input_bytes()
        || size > limits.maximum_decoded_bytes()
        || size > limits.maximum_work_units() / 2
    {
        return Err(error);
    }
    let (stream, base) = if input.starts_with(&[0xff, 0x4f]) {
        (input, 0)
    } else {
        let file = jp2::parse(input, limits)?;
        if !file.file_type().is_jp2_primary() || file.codestream_count() != 1 {
            return Err(error);
        }
        let stream = file.codestream(0)?;
        let header = stream.box_header();
        let base = header
            .offset()
            .checked_add(header.header_length())
            .and_then(|value| usize::try_from(value).ok())
            .ok_or(error)?;
        (stream.data(), base)
    };
    let (declared, positions) = count_fields(stream, offset, limits).ok_or(error)?;
    let mut repaired = Vec::new();
    repaired.try_reserve_exact(input.len()).map_err(|_| DecodeError::AllocationFailed)?;
    repaired.extend_from_slice(input);
    for pos in positions {
        let pos = base.checked_add(pos).ok_or(error)?;
        *repaired.get_mut(pos).ok_or(error)? = declared + 1;
    }
    crate::inspect_pdf_compatible(&repaired, options)?;
    Ok(repaired)
}

fn count_fields(
    stream: &[u8],
    error_offset: u64,
    limits: &ResourceLimits,
) -> Option<(u8, Vec<usize>)> {
    let mut pos = 2usize;
    while stream.get(pos..pos.checked_add(2)?)? != [0xff, 0x90] {
        let header = stream.get(pos..pos.checked_add(4)?)?;
        if header[0] != 0xff || !matches!(header[1], 0x50..=0x8f) {
            return None;
        }
        let length = usize::from(u16::from_be_bytes([header[2], header[3]]));
        if length < 2 {
            return None;
        }
        pos = pos.checked_add(2)?.checked_add(length)?;
    }
    // Tile indices are 16-bit. Store next expected indices only for observed
    // tiles, with both allocation and total parts bounded before growing.
    let mut next = Vec::<u16>::new();
    let mut fields = Vec::new();
    let mut declared = None;
    let mut matched_error = false;
    loop {
        if stream.get(pos..)? == [0xff, 0xd9] {
            break;
        }
        let part = stream.get(pos..pos.checked_add(12)?)?;
        if part[..4] != [0xff, 0x90, 0, 10] || part[11] == 0 || part[11] == 255 {
            return None;
        }
        if *declared.get_or_insert(part[11]) != part[11]
            || fields.len() as u64 >= u64::from(limits.maximum_tile_parts())
        {
            return None;
        }
        let tile = usize::from(u16::from_be_bytes([part[4], part[5]]));
        if tile as u64 >= u64::from(limits.maximum_tiles()) {
            return None;
        }
        if tile >= next.len() {
            next.try_reserve(tile + 1 - next.len()).ok()?;
            next.resize(tile + 1, 0);
        }
        if next[tile] != u16::from(part[10]) || part[10] > part[11] {
            return None;
        }
        next[tile] += 1;
        matched_error |= part[10] == part[11] && pos as u64 == error_offset;
        let length = usize::try_from(u32::from_be_bytes(part[6..10].try_into().ok()?)).ok()?;
        if length < 14 {
            return None;
        }
        fields.try_reserve(1).ok()?;
        fields.push(pos + 11);
        pos = pos.checked_add(length)?;
    }
    let declared = declared?;
    let total = u16::from(declared) + 1;
    if !matched_error || next.iter().any(|&count| count != 0 && count != total) {
        return None;
    }
    Some((declared, fields))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interleaved(tile_parts: &[(u8, u8, u8)]) -> Vec<u8> {
        let mut bytes = vec![0xff, 0x4f];
        for &(tile, index, declared) in tile_parts {
            bytes.extend_from_slice(&[
                0xff, 0x90, 0, 10, 0, tile, 0, 0, 0, 14, index, declared, 0xff, 0x93,
            ]);
        }
        bytes.extend_from_slice(&[0xff, 0xd9]);
        bytes
    }

    #[test]
    fn admits_only_the_reported_off_by_one_with_complete_interleaved_tiles() {
        let bytes = interleaved(&[(0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)]);
        let limits = ResourceLimits::default();
        assert_eq!(count_fields(&bytes, 30, &limits), Some((1, vec![13, 27, 41, 55])));
        assert_eq!(count_fields(&bytes, 29, &limits), None);
        assert_eq!(count_fields(&bytes[..bytes.len() - 1], 30, &limits), None);
        let limited = limits.with_maximum_tile_parts(3).unwrap();
        assert_eq!(count_fields(&bytes, 30, &limited), None);
    }

    #[test]
    fn rejects_missing_or_inconsistent_tile_parts() {
        let limits = ResourceLimits::default();
        for parts in [
            [(0, 0, 1), (1, 0, 1), (0, 1, 1), (2, 0, 1)],
            [(0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 2)],
            [(0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 2, 1)],
        ] {
            assert_eq!(count_fields(&interleaved(&parts), 30, &limits), None);
        }
    }
}
