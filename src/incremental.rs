//! Explicit final EOF and bounded buffered/replay raw/JP2 input.
//!
//! Requires `incremental-input`. This initial runtime profile retains source
//! bytes, not entropy-decoder state. Each new preview/final output invokes the
//! existing decoder once; replay bytes and wrapper work are reported. Backend
//! limits remain stage-local, not a new global CPU or live-allocation theorem.
//! This orchestration is outside the pinned Verus profile.

mod framing;

use crate::image::DecodedImage;
use crate::{
    DecodeError, DecodeOptions, DecodeSelection, MalformedKind, PdfRecovery, Resource, TypedImage,
};
use core::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum IncrementalFormat {
    Auto,
    Codestream,
    Jp2,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum IncrementalError {
    Decode(DecodeError),
    ConflictingInput { offset: u64 },
    InputClosed,
    FinalLengthTooSmall { declared: u64, retained_end: u64 },
}

impl From<DecodeError> for IncrementalError {
    fn from(error: DecodeError) -> Self {
        Self::Decode(error)
    }
}

impl fmt::Display for IncrementalError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(error) => error.fmt(formatter),
            Self::ConflictingInput { offset } => {
                write!(formatter, "conflicting incremental input at byte {offset}")
            }
            Self::InputClosed => formatter.write_str("incremental input is already closed"),
            Self::FinalLengthTooSmall {
                declared,
                retained_end,
            } => write!(
                formatter,
                "final input length {declared} precedes retained byte end {retained_end}"
            ),
        }
    }
}

impl std::error::Error for IncrementalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Decode(error) => Some(error),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct IncrementalProgress {
    pub contiguous_bytes: u64,
    pub retained_bytes: u64,
    pub retained_end: u64,
    pub pending_fragments: usize,
    pub committed_bytes: u64,
    pub final_length: Option<u64>,
    pub decode_attempts: u64,
    pub replayed_input_bytes: u64,
    /// Cumulative assembly, framing and replay-byte work; excludes backend stages.
    pub wrapper_work_units: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct IncrementalFeed {
    /// The complete supplied slice, including identical overlap, was accepted.
    pub consumed: usize,
    pub progress: IncrementalProgress,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum IncrementalNeed {
    Header,
    Packet,
    Gap { offset: u64, length: u64 },
    PreviewUnavailable { reason: &'static str },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct IncrementalSnapshot {
    pub source_bytes: u64,
    pub synthetic_eoc: bool,
    pub rewritten_tile_part_length: bool,
    pub rewritten_jp2_box: bool,
}

#[derive(Debug)]
#[non_exhaustive]
pub enum IncrementalUpdate<I> {
    NeedMoreData {
        reason: IncrementalNeed,
        progress: IncrementalProgress,
    },
    /// No new execution or image copy: retain the previously returned image.
    Unchanged { progress: IncrementalProgress },
    Preview {
        image: I,
        snapshot: IncrementalSnapshot,
        progress: IncrementalProgress,
    },
    Complete {
        image: I,
        recovery: Option<PdfRecovery>,
        progress: IncrementalProgress,
    },
}

#[derive(Debug)]
struct Fragment {
    offset: usize,
    bytes: Vec<u8>,
}

#[derive(Clone, Copy, Debug)]
struct Cached {
    length: usize,
    final_length: Option<u64>,
    outcome: CachedOutcome,
}

#[derive(Clone, Copy, Debug)]
enum CachedOutcome {
    Waiting(IncrementalNeed),
    Published,
    Rejected(IncrementalError),
}

type Decode<I> = fn(
    &[u8],
    IncrementalFormat,
    bool,
    &DecodeOptions,
    &DecodeSelection,
) -> Result<(I, Option<PdfRecovery>), DecodeError>;

/// One immutable input identity, with checked append and sparse out-of-order feed.
///
/// `feed` never decodes. `decode`/`decode_reconstructed` request packet previews
/// while input is open and exact ordinary decoding after explicit `finish`.
/// Previews are independent buffered snapshots, not saved entropy continuation.
/// An incomplete packet never replaces the last committed output. Final PDF
/// damage policies require the separately named `new_pdf_compatible` constructor.
///
/// Allocation refusal preserves retained bytes and permits retry; attempted
/// wrapper work stays charged. Deadline expiry cancels the object permanently.
#[derive(Debug)]
pub struct IncrementalDecoder<'a> {
    format: IncrementalFormat,
    options: &'a DecodeOptions,
    selection: &'a DecodeSelection,
    pdf_recovery: bool,
    prefix: Vec<u8>,
    pending: Vec<Fragment>,
    retained: u64,
    extent: u64,
    committed: u64,
    final_length: Option<u64>,
    attempts: u64,
    replayed: u64,
    work: u64,
    cached: [Option<Cached>; 2],
    #[cfg(feature = "cooperative-deadlines")]
    deadline: Option<std::time::Instant>,
    #[cfg(feature = "cooperative-deadlines")]
    cancelled: bool,
}

impl<'a> IncrementalDecoder<'a> {
    pub fn new(
        format: IncrementalFormat,
        options: &'a DecodeOptions,
        selection: &'a DecodeSelection,
    ) -> Self {
        Self {
            format,
            options,
            selection,
            pdf_recovery: false,
            prefix: Vec::new(),
            pending: Vec::new(),
            retained: 0,
            extent: 0,
            committed: 0,
            final_length: None,
            attempts: 0,
            replayed: 0,
            work: 0,
            cached: [None, None],
            #[cfg(feature = "cooperative-deadlines")]
            deadline: None,
            #[cfg(feature = "cooperative-deadlines")]
            cancelled: false,
        }
    }

    pub fn new_pdf_compatible(options: &'a DecodeOptions, selection: &'a DecodeSelection) -> Self {
        let mut decoder = Self::new(IncrementalFormat::Auto, options, selection);
        decoder.pdf_recovery = true;
        decoder
    }

    /// Set or tighten the absolute deadline shared by every subsequent operation.
    #[cfg(feature = "cooperative-deadlines")]
    pub fn with_deadline(mut self, deadline: std::time::Instant) -> Self {
        self.deadline = Some(match self.deadline {
            Some(previous) => previous.min(deadline),
            None => deadline,
        });
        self
    }

    pub fn progress(&self) -> IncrementalProgress {
        IncrementalProgress {
            contiguous_bytes: self.prefix.len() as u64,
            retained_bytes: self.retained,
            retained_end: self.extent,
            pending_fragments: self.pending.len(),
            committed_bytes: self.committed,
            final_length: self.final_length,
            decode_attempts: self.attempts,
            replayed_input_bytes: self.replayed,
            wrapper_work_units: self.work,
        }
    }

    pub fn contiguous_input(&self) -> &[u8] {
        &self.prefix
    }

    /// Append at the current contiguous end. Use `feed_at` for suffix-first input.
    pub fn feed(&mut self, bytes: &[u8]) -> Result<IncrementalFeed, IncrementalError> {
        self.feed_at(self.prefix.len() as u64, bytes)
    }

    pub fn feed_at(
        &mut self,
        offset: u64,
        bytes: &[u8],
    ) -> Result<IncrementalFeed, IncrementalError> {
        self.run(|decoder| decoder.feed_inner(offset, bytes))
    }

    pub fn finish(&mut self) -> Result<IncrementalProgress, IncrementalError> {
        self.finish_at(self.extent)
    }

    /// Declare actual final EOF, not a temporary pause or the arrival of a suffix.
    ///
    /// A final length containing gaps is retained; decoding then returns Truncated.
    /// No more input may be fed after a successful declaration.
    pub fn finish_at(&mut self, length: u64) -> Result<IncrementalProgress, IncrementalError> {
        self.run(|decoder| {
            decoder.input_bound(length)?;
            if length < decoder.extent {
                return Err(IncrementalError::FinalLengthTooSmall {
                    declared: length,
                    retained_end: decoder.extent,
                });
            }
            match decoder.final_length {
                Some(previous) if previous != length => return Err(IncrementalError::InputClosed),
                _ => decoder.final_length = Some(length),
            }
            Ok(decoder.progress())
        })
    }

    pub fn decode(&mut self) -> Result<IncrementalUpdate<TypedImage>, IncrementalError> {
        self.run(|decoder| decoder.decode_inner(0, typed))
    }

    pub fn decode_reconstructed(
        &mut self,
    ) -> Result<IncrementalUpdate<DecodedImage>, IncrementalError> {
        self.run(|decoder| decoder.decode_inner(1, reconstructed))
    }

    fn run<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> Result<T, IncrementalError>,
    ) -> Result<T, IncrementalError> {
        #[cfg(feature = "cooperative-deadlines")]
        {
            if self.cancelled {
                return Err(DecodeError::DeadlineExceeded.into());
            }
            let committed = self.committed;
            let cached = self.cached;
            let result = match self.deadline {
                Some(deadline) => crate::with_decode_deadline(deadline, || Ok(operation(self)))
                    .map_err(IncrementalError::Decode)
                    .and_then(|result| result),
                None => match crate::deadline::checkpoint() {
                    Err(error) => Err(error.into()),
                    Ok(()) => {
                        let result = operation(self);
                        match crate::deadline::checkpoint() {
                            Err(error) => Err(error.into()),
                            Ok(()) => result,
                        }
                    }
                },
            };
            if matches!(
                result,
                Err(IncrementalError::Decode(DecodeError::DeadlineExceeded))
            ) {
                self.committed = committed;
                self.cached = cached;
                self.cancelled = true;
            }
            result
        }
        #[cfg(not(feature = "cooperative-deadlines"))]
        operation(self)
    }

    fn input_bound(&self, length: u64) -> Result<(), IncrementalError> {
        let limit = self.options.limits().maximum_input_bytes();
        if length > limit {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::InputBytes,
                limit,
                actual: length,
            }
            .into());
        }
        Ok(())
    }

    fn charge(&mut self, amount: u64) -> Result<(), IncrementalError> {
        charge_work(&mut self.work, amount, self.options.limits())?;
        Ok(())
    }

    fn feed_inner(
        &mut self,
        offset: u64,
        bytes: &[u8],
    ) -> Result<IncrementalFeed, IncrementalError> {
        if self.final_length.is_some() {
            return Err(IncrementalError::InputClosed);
        }
        let end = offset
            .checked_add(bytes.len() as u64)
            .ok_or_else(overflow)?;
        self.input_bound(end)?;
        if bytes.is_empty() {
            return Ok(IncrementalFeed {
                consumed: 0,
                progress: self.progress(),
            });
        }
        let offset = usize::try_from(offset).map_err(|_| overflow())?;
        let end = usize::try_from(end).map_err(|_| overflow())?;
        self.charge(
            (bytes.len() as u64)
                .checked_mul(2)
                .ok_or_else(overflow)?
                .checked_add(self.pending.len() as u64)
                .ok_or_else(overflow)?,
        )?;
        let mut covered = overlap(0, &self.prefix, offset, bytes)?;
        for fragment in &self.pending {
            covered = covered
                .checked_add(overlap(fragment.offset, &fragment.bytes, offset, bytes)?)
                .ok_or_else(overflow)?;
        }
        if covered == bytes.len() {
            return Ok(IncrementalFeed {
                consumed: bytes.len(),
                progress: self.progress(),
            });
        }
        if self.pending.is_empty() && offset <= self.prefix.len() {
            if end > self.prefix.len() {
                let start = self.prefix.len() - offset;
                let extended = crate::allocation::extend_bytes(&mut self.prefix, &bytes[start..]);
                self.retained = self.prefix.len() as u64;
                self.extent = self.retained;
                extended?;
            }
        } else {
            self.sparse_feed(offset, bytes)?;
        }
        Ok(IncrementalFeed {
            consumed: bytes.len(),
            progress: self.progress(),
        })
    }

    fn sparse_feed(&mut self, offset: usize, bytes: &[u8]) -> Result<(), IncrementalError> {
        self.charge(
            self.retained
                .checked_add(bytes.len() as u64)
                .ok_or_else(overflow)?,
        )?;
        let count = self.pending.len().checked_add(2).ok_or_else(overflow)?;
        let metadata = (count as u64)
            .checked_mul((core::mem::size_of::<Fragment>() * 4) as u64)
            .ok_or_else(overflow)?;
        let limit = self.options.limits().maximum_metadata_bytes();
        if metadata > limit {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::MetadataBytes,
                limit,
                actual: metadata,
            }
            .into());
        }
        let mut pieces = crate::allocation::empty_with_capacity(count)?;
        if !self.prefix.is_empty() {
            pieces.push((0, self.prefix.as_slice()));
        }
        for fragment in &self.pending {
            pieces.push((fragment.offset, fragment.bytes.as_slice()));
        }
        let position = pieces.partition_point(|piece| piece.0 <= offset);
        pieces.insert(position, (offset, bytes));
        let mut staged = crate::allocation::empty_with_capacity(pieces.len())?;
        let mut first = 0;
        let mut retained = 0_u64;
        while first < pieces.len() {
            checkpoint()?;
            let start = pieces[first].0;
            let mut end = start
                .checked_add(pieces[first].1.len())
                .ok_or_else(overflow)?;
            let mut last = first + 1;
            while last < pieces.len() && pieces[last].0 <= end {
                end = end.max(
                    pieces[last]
                        .0
                        .checked_add(pieces[last].1.len())
                        .ok_or_else(overflow)?,
                );
                last += 1;
            }
            let mut combined = crate::allocation::empty_with_capacity(end - start)?;
            for &(position, source) in &pieces[first..last] {
                checkpoint()?;
                let copied_end = start + combined.len();
                if position + source.len() > copied_end {
                    combined.extend_from_slice(&source[copied_end.saturating_sub(position)..]);
                }
            }
            retained = retained
                .checked_add(combined.len() as u64)
                .ok_or_else(overflow)?;
            staged.push(Fragment {
                offset: start,
                bytes: combined,
            });
            first = last;
        }
        drop(pieces);
        checkpoint()?;
        let extent = self.extent.max((offset + bytes.len()) as u64);
        let prefix = if staged.first().is_some_and(|fragment| fragment.offset == 0) {
            staged.remove(0).bytes
        } else {
            Vec::new()
        };
        self.prefix = prefix;
        self.pending = staged;
        self.retained = retained;
        self.extent = extent;
        Ok(())
    }

    fn waiting<I>(&self, reason: IncrementalNeed) -> IncrementalUpdate<I> {
        let reason = match self.pending.first() {
            Some(fragment) => IncrementalNeed::Gap {
                offset: self.prefix.len() as u64,
                length: (fragment.offset - self.prefix.len()) as u64,
            },
            _ => reason,
        };
        IncrementalUpdate::NeedMoreData {
            reason,
            progress: self.progress(),
        }
    }

    fn decode_inner<I>(
        &mut self,
        slot: usize,
        decode: Decode<I>,
    ) -> Result<IncrementalUpdate<I>, IncrementalError> {
        if let Some(cached) = self.cached[slot]
            && cached.length == self.prefix.len()
            && cached.final_length == self.final_length
        {
            return match cached.outcome {
                CachedOutcome::Waiting(reason) => Ok(self.waiting(reason)),
                CachedOutcome::Published => Ok(IncrementalUpdate::Unchanged {
                    progress: self.progress(),
                }),
                CachedOutcome::Rejected(error) => Err(error),
            };
        }
        let length = self.prefix.len();
        let final_length = self.final_length;
        if let Some(final_length) = final_length
            && (final_length != length as u64 || !self.pending.is_empty())
        {
            let error = IncrementalError::Decode(truncated(length));
            self.cached[slot] = Some(Cached {
                length,
                final_length: self.final_length,
                outcome: CachedOutcome::Rejected(error),
            });
            return Err(error);
        }
        let snapshot = if final_length.is_none() {
            match framing::snapshot(
                &self.prefix,
                self.format,
                self.options.limits(),
                &mut self.work,
            ) {
                Ok(framing::Preview::Waiting(reason)) => {
                    self.cached[slot] = Some(Cached {
                        length,
                        final_length,
                        outcome: CachedOutcome::Waiting(reason),
                    });
                    return Ok(self.waiting(reason));
                }
                Ok(framing::Preview::Ready(snapshot)) => Some(snapshot),
                Err(error) => return self.reject(slot, error.into()),
            }
        } else {
            self.charge((length as u64).checked_add(1).ok_or_else(overflow)?)?;
            None
        };
        let encoded = match &snapshot {
            Some(snapshot) => snapshot.bytes.as_slice(),
            None => self.prefix.as_slice(),
        };
        self.attempts = self.attempts.checked_add(1).ok_or_else(overflow)?;
        self.replayed = self
            .replayed
            .checked_add(encoded.len() as u64)
            .ok_or_else(overflow)?;
        let decoded = decode(
            encoded,
            self.format,
            final_length.is_some() && self.pdf_recovery,
            self.options,
            self.selection,
        );
        match decoded {
            Ok((image, recovery)) => {
                self.committed = length as u64;
                self.cached[slot] = Some(Cached {
                    length,
                    final_length,
                    outcome: CachedOutcome::Published,
                });
                match snapshot {
                    Some(snapshot) => Ok(IncrementalUpdate::Preview {
                        image,
                        snapshot: snapshot.info,
                        progress: self.progress(),
                    }),
                    None => Ok(IncrementalUpdate::Complete {
                        image,
                        recovery,
                        progress: self.progress(),
                    }),
                }
            }
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::Truncated,
                ..
            }) if final_length.is_none() => {
                self.cached[slot] = Some(Cached {
                    length,
                    final_length,
                    outcome: CachedOutcome::Waiting(IncrementalNeed::Packet),
                });
                Ok(self.waiting(IncrementalNeed::Packet))
            }
            Err(error) => self.reject(slot, error.into()),
        }
    }

    fn reject<I>(&mut self, slot: usize, error: IncrementalError) -> Result<I, IncrementalError> {
        if !matches!(
            error,
            IncrementalError::Decode(DecodeError::AllocationFailed)
        ) {
            self.cached[slot] = Some(Cached {
                length: self.prefix.len(),
                final_length: self.final_length,
                outcome: CachedOutcome::Rejected(error),
            });
        }
        Err(error)
    }
}

fn overlap(
    stored_offset: usize,
    stored: &[u8],
    offset: usize,
    incoming: &[u8],
) -> Result<usize, IncrementalError> {
    let start = stored_offset.max(offset);
    let end = (stored_offset + stored.len()).min(offset + incoming.len());
    if start < end {
        for (block, (left, right)) in stored[start - stored_offset..end - stored_offset]
            .chunks(1024)
            .zip(incoming[start - offset..end - offset].chunks(1024))
            .enumerate()
        {
            checkpoint()?;
            if let Some(difference) = left
                .iter()
                .zip(right)
                .position(|(left, right)| left != right)
            {
                return Err(IncrementalError::ConflictingInput {
                    offset: (start + block * 1024 + difference) as u64,
                });
            }
        }
    }
    Ok(end.saturating_sub(start))
}

fn overflow() -> IncrementalError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    }
    .into()
}

fn truncated(offset: usize) -> DecodeError {
    DecodeError::MalformedInput {
        offset: offset as u64,
        kind: MalformedKind::Truncated,
    }
}

fn checkpoint() -> Result<(), DecodeError> {
    #[cfg(feature = "cooperative-deadlines")]
    crate::deadline::checkpoint()?;
    Ok(())
}

fn charge_work(
    work: &mut u64,
    amount: u64,
    limits: &crate::ResourceLimits,
) -> Result<(), DecodeError> {
    checkpoint()?;
    *work = work
        .checked_add(amount)
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })?;
    let limit = limits.maximum_work_units();
    if *work > limit {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit,
            actual: *work,
        });
    }
    Ok(())
}

fn raw(format: IncrementalFormat, input: &[u8]) -> bool {
    match format {
        IncrementalFormat::Codestream => true,
        IncrementalFormat::Jp2 => false,
        IncrementalFormat::Auto => input.starts_with(&[0xff, 0x4f]),
    }
}

fn typed(
    input: &[u8],
    format: IncrementalFormat,
    pdf: bool,
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<(TypedImage, Option<PdfRecovery>), DecodeError> {
    if pdf {
        let decoded = crate::decode_pdf_compatible(input, options, selection)?;
        Ok((decoded.image, Some(decoded.recovery)))
    } else {
        let image = if raw(format, input) {
            crate::decode_codestream_selected(input, options, selection)?
        } else {
            crate::decode_jp2_selected(input, options, selection)?
        };
        Ok((image, None))
    }
}

fn reconstructed(
    input: &[u8],
    format: IncrementalFormat,
    pdf: bool,
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<(DecodedImage, Option<PdfRecovery>), DecodeError> {
    if pdf {
        let decoded = crate::decode_pdf_reconstructed(input, options, selection)?;
        Ok((decoded.image, Some(decoded.recovery)))
    } else {
        let image = if raw(format, input) {
            crate::decode_codestream_reconstructed_selected(input, options, selection)?
        } else {
            crate::decode_jp2_reconstructed_selected(input, options, selection)?
        };
        Ok((image, None))
    }
}

#[cfg(test)]
mod tests;
