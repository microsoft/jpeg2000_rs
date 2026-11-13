//! Explicit raw-only EOC recovery. This is not a conformance or deadline mode.
use crate::image::DecodedImage;
use crate::{DecodeError, DecodeOptions, MalformedKind, Resource, ResourceLimits, TypedImage};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(test)]
mod tests;

/// What was changed, and the actual decoded reference-grid geometry.
///
/// The additional preflight/copy stage jointly obeys `maximum_work_units`.
/// `preflight_work_units` counts the shared reader's marker work and physical
/// body bytes traversed; `repair_copy_bytes` counts all bytes copied, including
/// EOC. Strict decoding retains its existing, separate stage-local counters.
/// These fields are not a global decoder-work or live-allocation measurement.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct RawRecoveryReport {
    pub appended_eoc: bool,
    pub original_bytes: u64,
    pub effective_bytes: u64,
    pub width: u32,
    pub height: u32,
    pub x_origin: u32,
    pub y_origin: u32,
    pub preflight_work_units: u64,
    pub repair_copy_bytes: u64,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct RawRecoveredImage {
    pub image: TypedImage,
    pub report: RawRecoveryReport,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct RawRecoveredReconstructedImage {
    pub image: DecodedImage,
    pub report: RawRecoveryReport,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn recovered_outcome(result: Result<RawRecoveredImage, DecodeError>)
        -> Result<(crate::specs::Part1DecodedTypedImage, RawRecoveryReport), DecodeError>
    {
        match result {
            Ok(decoded) => Ok((crate::image::typed_image_value_view(decoded.image), decoded.report)),
            Err(error) => Err(error),
        }
    }

    pub(crate) open spec fn repair_outcome(result: Result<Vec<u8>, DecodeError>)
        -> Result<Seq<u8>, DecodeError>
    {
        match result { Ok(bytes) => Ok(bytes@), Err(error) => Err(error) }
    }

    pub open spec fn reconstructed_recovered_outcome(
        result: Result<RawRecoveredReconstructedImage, DecodeError>,
    ) -> Result<(crate::specs::Part1DecodedImageModel, RawRecoveryReport), DecodeError>
    {
        match result {
            Ok(decoded) => Ok((crate::image::decoded_image_view(decoded.image), decoded.report)),
            Err(error) => Err(error),
        }
    }
}

/// Decode raw JPEG 2000, opting into exactly the sole-open-ended-part EOC repair.
///
/// A checked structural preflight uses the normal SIZ/marker/SOT readers. Only
/// one advertised image tile, part index zero, part count zero or one, Psot=0,
/// complete length-delimited headers and SOD can admit an appended `FF D9`.
/// A marker-aware body traversal prevents appending after an existing EOC,
/// another SOT or an unrelated marker. Header semantics, packet lengths and
/// entropy are still checked by one ordinary strict decode, without retries.
/// No suffix is discarded and no missing pixels are synthesized.
///
/// A repair copy has exactly input length plus two logical bytes and one
/// fallible reservation. The std reservation/no-growth boundary is unchanged;
/// allocator capacity, unwind behavior and host OOM are not mathematical claims.
/// Input/image limits are unchanged. Extra preflight/copy work is jointly
/// bounded by the existing work cap; strict decode keeps its existing counters,
/// not a newly invented global scope. There is no cooperative deadline API yet.
///
/// This API does not parse JP2/JPX containers, change dimensions, recover absent
/// tiles, admit MQ damage or discard trailers. Existing strict APIs are unchanged.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::raw_recovery_result(
        input@, crate::options::decode_options_limits(options), recovered_outcome(result)),
))]
pub fn decode_codestream_recover_missing_eoc(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<RawRecoveredImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::raw_recovery_result_unfold(input@, crate::options::decode_options_limits(options));
        reveal(crate::codestream::recovery_framing::framing_outcome);
    }
    let frame = crate::codestream::recovery_framing(input, options.limits())?;
    if !frame.append_eoc {
        return finish_recovery(input.len(), frame, crate::decode_codestream(input, options));
    }
    admit_repair(input.len(), frame.work_units, options.limits())?;
    let repaired = append_eoc(input)?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::raw_repair_result); reveal(repair_outcome); }
    finish_recovery(
        input.len(),
        frame,
        crate::decode_codestream(&repaired, options),
    )
}

/// Recover the same bounded missing-EOC case while retaining reconstruction samples.
///
/// Admission, one fallible repair copy, limits and report accounting are identical
/// to `decode_codestream_recover_missing_eoc`. The one strict decode uses
/// `decode_codestream_reconstructed`, preserving centered samples, fraction bits
/// and actual geometry before output conversion. Its NLT rejection and genuine
/// parser/reconstruction errors are propagated without retry.
///
/// This API has no container, selection, color, deadline or additional recovery
/// policy. Full fallible allocation remains incomplete under #287.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::raw_reconstructed_recovery_result(
        input@, crate::options::decode_options_limits(options),
        reconstructed_recovered_outcome(result)),
))]
pub fn decode_codestream_reconstructed_recover_missing_eoc(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<RawRecoveredReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::raw_reconstructed_recovery_result_unfold(
            input@, crate::options::decode_options_limits(options));
        reveal(crate::codestream::recovery_framing::framing_outcome);
    }
    let frame = crate::codestream::recovery_framing(input, options.limits())?;
    if !frame.append_eoc {
        return finish_reconstructed_recovery(
            input.len(),
            frame,
            crate::decode_codestream_reconstructed(input, options),
        );
    }
    admit_repair(input.len(), frame.work_units, options.limits())?;
    let repaired = append_eoc(input)?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::raw_repair_result); reveal(repair_outcome); }
    finish_reconstructed_recovery(
        input.len(),
        frame,
        crate::decode_codestream_reconstructed(&repaired, options),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::raw_recovery_admit(input_bytes, work, limits),
))]
fn admit_repair(input_bytes: usize, work: u64, limits: &ResourceLimits) -> Result<(), DecodeError> {
    let total = input_bytes
        .checked_add(2)
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })?;
    if total as u64 > limits.maximum_input_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: limits.maximum_input_bytes(),
            actual: total as u64,
        });
    }
    let combined = work
        .checked_add(total as u64)
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })?;
    if combined > limits.maximum_work_units() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit: limits.maximum_work_units(),
            actual: combined,
        });
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::raw_repair_result(input@, repair_outcome(result)),
))]
fn append_eoc(input: &[u8]) -> Result<Vec<u8>, DecodeError> {
    let total = input
        .len()
        .checked_add(2)
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })?;
    let mut repaired = crate::allocation::empty_with_capacity(total)?;
    repaired.extend_from_slice(input);
    repaired.extend_from_slice(&[0xff, 0xd9]);
    #[cfg(verus_keep_ghost)]
    proof! { assert(repaired@ =~= input@ + seq![0xffu8, 0xd9u8]); }
    Ok(repaired)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures recovered_outcome(result) == crate::specs::raw_recovery_finish(
        original, (frame.append_eoc, frame.work_units), crate::image::decoded_typed_image_outcome(decoded)),
))]
fn finish_recovery(
    original: usize,
    frame: crate::codestream::RecoveryFraming,
    decoded: Result<TypedImage, DecodeError>,
) -> Result<RawRecoveredImage, DecodeError> {
    let image = decoded?;
    let report = recovery_report(
        original,
        frame,
        (
            image.width(),
            image.height(),
            image.x_origin(),
            image.y_origin(),
        ),
    )?;
    Ok(RawRecoveredImage { image, report })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures reconstructed_recovered_outcome(result) == crate::specs::raw_reconstructed_recovery_finish(
        original, (frame.append_eoc, frame.work_units), crate::image::decoded_image_outcome(decoded)),
))]
fn finish_reconstructed_recovery(
    original: usize,
    frame: crate::codestream::RecoveryFraming,
    decoded: Result<DecodedImage, DecodeError>,
) -> Result<RawRecoveredReconstructedImage, DecodeError> {
    let image = decoded?;
    let report = recovery_report(
        original,
        frame,
        (
            image.width(),
            image.height(),
            image.x_origin(),
            image.y_origin(),
        ),
    )?;
    Ok(RawRecoveredReconstructedImage { image, report })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::raw_recovery_report(
        original, (frame.append_eoc, frame.work_units), geometry),
))]
fn recovery_report(
    original: usize,
    frame: crate::codestream::RecoveryFraming,
    geometry: (u32, u32, u32, u32),
) -> Result<RawRecoveryReport, DecodeError> {
    let effective = (original as u64)
        .checked_add(if frame.append_eoc { 2 } else { 0 })
        .ok_or(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow,
        })?;
    Ok(RawRecoveryReport {
        appended_eoc: frame.append_eoc,
        original_bytes: original as u64,
        effective_bytes: effective,
        width: geometry.0,
        height: geometry.1,
        x_origin: geometry.2,
        y_origin: geometry.3,
        preflight_work_units: frame.work_units,
        repair_copy_bytes: if frame.append_eoc { effective } else { 0 },
    })
}
