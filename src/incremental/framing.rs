use super::{IncrementalFormat, IncrementalNeed, IncrementalSnapshot};
use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};

pub(super) struct Snapshot {
    pub bytes: Vec<u8>,
    pub info: IncrementalSnapshot,
}

pub(super) enum Preview {
    Waiting(IncrementalNeed),
    Ready(Snapshot),
}

struct Window<'a> {
    raw: &'a [u8],
    start: usize,
    box_start: Option<usize>,
    extended: bool,
    partial_box: bool,
}

fn malformed(offset: usize, kind: MalformedKind) -> DecodeError {
    DecodeError::MalformedInput {
        offset: offset as u64,
        kind,
    }
}

fn u32_at(input: &[u8], offset: usize) -> u32 {
    u32::from_be_bytes([
        input[offset],
        input[offset + 1],
        input[offset + 2],
        input[offset + 3],
    ])
}

fn window<'a>(
    input: &'a [u8],
    format: IncrementalFormat,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<Option<Window<'a>>, DecodeError> {
    super::charge_work(work, input.len().min(12) as u64, limits)?;
    let codestream = match format {
        IncrementalFormat::Codestream => true,
        IncrementalFormat::Jp2 => false,
        IncrementalFormat::Auto => input.first() == Some(&0xff),
    };
    if codestream {
        for (index, expected) in [0xff, 0x4f].into_iter().enumerate().take(input.len()) {
            if input[index] != expected {
                return Err(malformed(index, MalformedKind::InvalidMarker));
            }
        }
        return Ok(if input.len() < 2 {
            None
        } else {
            Some(Window {
                raw: input,
                start: 0,
                box_start: None,
                extended: false,
                partial_box: false,
            })
        });
    }
    const SIGNATURE: &[u8] = &[0, 0, 0, 12, b'j', b'P', b' ', b' ', 13, 10, 135, 10];
    for (index, (&actual, &expected)) in input.iter().zip(SIGNATURE).enumerate() {
        if actual != expected {
            return Err(malformed(index, MalformedKind::InvalidSignature));
        }
    }
    if input.len() < SIGNATURE.len() {
        return Ok(None);
    }
    let mut position = 0;
    let mut found = None;
    while position < input.len() {
        super::charge_work(work, (input.len() - position).min(16) as u64, limits)?;
        if input.len() - position < 8 {
            return Ok(None);
        }
        let declared = u32_at(input, position);
        let extended = declared == 1;
        let header = if extended { 16 } else { 8 };
        if input.len() - position < header {
            return Ok(None);
        }
        let length = if extended {
            u64::from_be_bytes(
                input[position + 8..position + 16]
                    .try_into()
                    .map_err(|_| malformed(position, MalformedKind::InvalidBoxLength))?,
            )
        } else if declared == 0 {
            (input.len() - position) as u64
        } else {
            u64::from(declared)
        };
        if length < header as u64 {
            return Err(malformed(position, MalformedKind::InvalidBoxLength));
        }
        let length = usize::try_from(length)
            .map_err(|_| malformed(position, MalformedKind::ArithmeticOverflow))?;
        let end = position
            .checked_add(length)
            .ok_or_else(|| malformed(position, MalformedKind::ArithmeticOverflow))?;
        if &input[position + 4..position + 8] == b"jp2c" {
            if found.is_some() {
                return Ok(found);
            }
            if end > input.len() {
                return Ok(Some(Window {
                    raw: &input[position + header..],
                    start: position + header,
                    box_start: Some(position),
                    extended,
                    partial_box: true,
                }));
            }
            found = Some(Window {
                raw: &input[position + header..end],
                start: position + header,
                box_start: Some(position),
                extended,
                partial_box: declared == 0,
            });
        } else if end > input.len() {
            return Ok(None);
        }
        position = end;
    }
    Ok(found)
}

pub(super) fn snapshot(
    input: &[u8],
    format: IncrementalFormat,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<Preview, DecodeError> {
    let Some(window) = window(input, format, limits, work)? else {
        return Ok(Preview::Waiting(IncrementalNeed::Header));
    };
    let raw = window.raw;
    super::charge_work(work, 2, limits)?;
    if raw.ends_with(&[0xff, 0xd9]) {
        return build(input, &window, None, false, limits, work);
    }
    let mut position = 2_usize;
    let mut sot = None;
    let mut data_start = None;
    let mut restricted = false;
    let mut part_end = None;
    while position < raw.len() {
        super::charge_work(work, (raw.len() - position).min(4) as u64, limits)?;
        if raw.len() - position < 2 {
            return Ok(Preview::Waiting(IncrementalNeed::Header));
        }
        if raw[position] != 0xff || matches!(raw[position + 1], 0 | 0xff) {
            return Err(malformed(position, MalformedKind::InvalidMarker));
        }
        let marker = u16::from_be_bytes([raw[position], raw[position + 1]]);
        if marker == 0xff93 {
            if sot.is_none() {
                return Err(malformed(position, MalformedKind::InvalidMarkerOrder));
            }
            data_start = Some(position + 2);
            break;
        }
        if matches!(marker, 0xff4f | 0xffd9 | 0xff92) {
            return Err(malformed(position, MalformedKind::InvalidMarkerOrder));
        }
        if raw.len() - position < 4 {
            return Ok(Preview::Waiting(IncrementalNeed::Header));
        }
        let length = usize::from(u16::from_be_bytes([raw[position + 2], raw[position + 3]]));
        if length < 2 {
            return Err(malformed(position, MalformedKind::InvalidMarkerLength));
        }
        let end = position
            .checked_add(2)
            .and_then(|offset| offset.checked_add(length))
            .ok_or_else(|| malformed(position, MalformedKind::ArithmeticOverflow))?;
        if end > raw.len() {
            return Ok(Preview::Waiting(IncrementalNeed::Header));
        }
        restricted |= matches!(marker, 0xff55 | 0xff57 | 0xff58 | 0xff60 | 0xff61);
        if marker == 0xff51 && length >= 38 {
            super::charge_work(work, 32, limits)?;
            let width = u32_at(raw, position + 6);
            let height = u32_at(raw, position + 10);
            let tile_width = u32_at(raw, position + 22);
            let tile_height = u32_at(raw, position + 26);
            let tile_x = u32_at(raw, position + 30);
            let tile_y = u32_at(raw, position + 34);
            if tile_width != 0
                && tile_height != 0
                && (u64::from(width) > u64::from(tile_x) + u64::from(tile_width)
                    || u64::from(height) > u64::from(tile_y) + u64::from(tile_height))
            {
                restricted = true;
            }
        }
        if marker == 0xff90 {
            super::charge_work(work, 8, limits)?;
            if length != 10 {
                return Err(malformed(position, MalformedKind::InvalidTilePart));
            }
            if sot.is_some() {
                return Ok(Preview::Waiting(IncrementalNeed::PreviewUnavailable {
                    reason: "partial previews require one tile-part",
                }));
            }
            if raw[position + 10] != 0 || raw[position + 11] > 1 {
                restricted = true;
            }
            let length = u32_at(raw, position + 6) as usize;
            if length != 0 {
                part_end = Some(
                    position
                        .checked_add(length)
                        .ok_or_else(|| malformed(position, MalformedKind::ArithmeticOverflow))?,
                );
            }
            sot = Some(position);
        }
        position = end;
    }
    let Some(data_start) = data_start else {
        return Ok(Preview::Waiting(IncrementalNeed::Header));
    };
    if restricted {
        return Ok(Preview::Waiting(IncrementalNeed::PreviewUnavailable {
            reason: "partial previews require one inline tile without length/packed-header tables",
        }));
    }
    if let Some(end) = part_end {
        if end < data_start {
            return Err(malformed(data_start, MalformedKind::InvalidTilePart));
        }
        if raw.len() > end {
            if raw.len() - end < 2 {
                return Ok(Preview::Waiting(IncrementalNeed::Header));
            }
            return build(input, &window, None, false, limits, work);
        }
    } else if raw.last() == Some(&0xff) {
        return Ok(Preview::Waiting(IncrementalNeed::Packet));
    }
    if raw.len() == data_start {
        return Ok(Preview::Waiting(IncrementalNeed::Packet));
    }
    build(input, &window, sot, true, limits, work)
}

fn build(
    input: &[u8],
    window: &Window<'_>,
    sot: Option<usize>,
    synthetic: bool,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<Preview, DecodeError> {
    let added = usize::from(synthetic) * 2;
    let source_end = window.start + window.raw.len();
    let length = input
        .len()
        .checked_add(added)
        .ok_or_else(|| malformed(0, MalformedKind::ArithmeticOverflow))?;
    if sot.is_some_and(|start| window.raw.len() - start > u32::MAX as usize)
        || window
            .box_start
            .is_some_and(|start| !window.extended && source_end + added - start > u32::MAX as usize)
    {
        return Ok(Preview::Waiting(IncrementalNeed::PreviewUnavailable {
            reason: "partial snapshot lengths must fit the original 32-bit framing",
        }));
    }
    if length as u64 > limits.maximum_input_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: limits.maximum_input_bytes(),
            actual: length as u64,
        });
    }
    super::charge_work(
        work,
        (length as u64)
            .checked_mul(2)
            .ok_or_else(|| malformed(0, MalformedKind::ArithmeticOverflow))?,
        limits,
    )?;
    let mut bytes = crate::allocation::empty_with_capacity(length)?;
    bytes.extend_from_slice(&input[..source_end]);
    if synthetic {
        bytes.extend_from_slice(&[0xff, 0xd9]);
    }
    bytes.extend_from_slice(&input[source_end..]);
    let mut rewritten_part = false;
    if let Some(sot) = sot {
        let actual = u32::try_from(window.raw.len() - sot)
            .map_err(|_| malformed(sot, MalformedKind::ArithmeticOverflow))?;
        rewritten_part = u32_at(window.raw, sot + 6) != actual;
        bytes[window.start + sot + 6..window.start + sot + 10]
            .copy_from_slice(&actual.to_be_bytes());
    }
    let rewritten_box = window.partial_box || synthetic;
    if rewritten_box && let Some(start) = window.box_start {
        let box_length = source_end + added - start;
        if window.extended {
            bytes[start + 8..start + 16].copy_from_slice(&(box_length as u64).to_be_bytes());
        } else {
            let length = u32::try_from(box_length)
                .map_err(|_| malformed(start, MalformedKind::InvalidBoxLength))?;
            bytes[start..start + 4].copy_from_slice(&length.to_be_bytes());
        }
    }
    Ok(Preview::Ready(Snapshot {
        bytes,
        info: IncrementalSnapshot {
            source_bytes: input.len() as u64,
            synthetic_eoc: synthetic,
            rewritten_tile_part_length: rewritten_part,
            rewritten_jp2_box: rewritten_box && window.box_start.is_some(),
        },
    }))
}
