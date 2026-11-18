use super::pdf_present_tile::{automatic_tile, effective_selection, finish_report};
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Recoveries actually applied by a compatible PDF decode.
///
/// Byte/work fields describe the successful codestream preflight and optional
/// repair copy, not a global decoder-work or peak/live-allocation measurement.
/// Separately reported PDF EOL bytes are not part of the normalized codestream.
/// An EOL retry retains each attempt's ordinary limits; its failed first
/// attempt is not included in the successful preflight's work counter.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Default, Eq, PartialEq))]
#[non_exhaustive]
pub struct PdfRecovery {
    pub appended_eoc: bool,
    pub ignored_container_dimensions: bool,
    pub selected_present_tile: Option<u16>,
    /// Actual initial one-pass MQ recoveries under native `pdf-mq-recovery`; zero otherwise.
    pub empty_initial_mq_prefixes: u32,
    pub discarded_tile_trailer_bytes: u64,
    /// One PDF end-of-line marker discarded after a validated image boundary.
    pub discarded_pdf_eol_bytes: u8,
    pub original_codestream_bytes: u64,
    pub effective_codestream_bytes: u64,
    pub preflight_work_units: u64,
    pub repair_copy_bytes: u64,
    pub full_canvas_sample_bytes: Option<u64>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct PdfDecodedImage {
    pub image: TypedImage,
    pub recovery: PdfRecovery,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct PdfReconstructedImage {
    pub image: DecodedImage,
    pub recovery: PdfRecovery,
}

struct PreparedPdfInput<'a> {
    file: Option<jp2::Jp2File<'a>>,
    original: &'a [u8],
    repaired: Option<Vec<u8>>,
    preflight_work: u64,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn pdf_eol_end_outcome(result: Option<usize>) -> Option<nat> {
        match result { None => None, Some(end) => Some(end as nat) }
    }

    pub(crate) closed spec fn prepared_pdf_input_view(value: &PreparedPdfInput<'_>) -> crate::specs::Part2PdfPrepared {
        crate::specs::Part2PdfPrepared {
            file: match value.file { None => None, Some(file) => Some(jp2::raw_jp2_file_view(&file)) },
            original: value.original@,
            repaired: match value.repaired { None => None, Some(bytes) => Some(bytes@) },
            preflight_work: value.preflight_work,
        }
    }

    pub(crate) open spec fn prepared_pdf_input_outcome(result: Result<PreparedPdfInput<'_>, DecodeError>)
        -> Result<crate::specs::Part2PdfPrepared, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) => Ok(prepared_pdf_input_view(&value)) }
    }

    pub open spec fn pdf_typed_outcome(result: Result<PdfDecodedImage, DecodeError>)
        -> Result<crate::specs::Part2PdfTyped, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) =>
            Ok((crate::image::typed_image_value_view(value.image), value.recovery)) }
    }

    pub open spec fn pdf_reconstructed_outcome(result: Result<PdfReconstructedImage, DecodeError>)
        -> Result<crate::specs::Part2PdfReconstructed, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) =>
            Ok((crate::image::decoded_image_view(value.image), value.recovery)) }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result@ == crate::specs::part2_pdf_effective_input(prepared_pdf_input_view(prepared)),
))]
fn effective_input<'p, 'a>(prepared: &'p PreparedPdfInput<'a>) -> &'p [u8] {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(prepared_pdf_input_view); }
    match &prepared.repaired {
        None => prepared.original,
        Some(bytes) => bytes.as_slice(),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == crate::specs::part2_pdf_invalid_profile(),))]
fn invalid_profile() -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidProfile,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_prepare_result(input@, crate::options::decode_options_limits(options), prepared_pdf_input_outcome(result)),
        prepared_pdf_input_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            prepared_pdf_input_outcome(result) == crate::specs::part2_pdf_prepare_value(input@, crate::options::decode_options_limits(options)),
))]
fn prepare_pdf_input<'a>(
    input: &'a [u8],
    options: &DecodeOptions,
) -> Result<PreparedPdfInput<'a>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_prepare_normal(input@, crate::options::decode_options_limits(options));
    }
    let file = if input.first() == Some(&0xff) && input.get(1) == Some(&0x4f) {
        None
    } else {
        let parsed_file = jp2::parse(input, options.limits());
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = parsed_file {
                crate::specs::part2_pdf_prepare_container_error(
                    input@, crate::options::decode_options_limits(options), error);
            }
        }
        let file = parsed_file?;
        #[cfg(verus_keep_ghost)]
        proof! { jp2::raw_render_file_known(&file); }
        let kind = file.file_type();
        if !kind.is_compatible_with(jp2::BoxType::JP2_BRAND)
            || (kind.is_jpx_compatible() && !kind.is_jp2_primary())
            || kind.is_jph_compatible()
            || file.codestream_count() != 1
        {
            return Err(invalid_profile());
        }
        Some(file)
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost file_value = match file { None => None, Some(value) => Some(jp2::raw_jp2_file_view(&value)) };
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_pdf_file_value(input@, crate::options::decode_options_limits(options)) == Ok(file_value));
    }
    let original = match &file {
        None => input,
        Some(file) => file.codestream(0)?.data(),
    };
    let frame = codestream::recovery_framing(original, options.limits())?;
    let repaired = if frame.append_eoc {
        crate::recovery::admit_repair(original.len(), frame.work_units, options.limits())?;
        let copied = crate::recovery::append_eoc(original);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(codestream::recovery_framing::framing_outcome);
            crate::specs::part2_pdf_prepare_copy_actual(input@, crate::options::decode_options_limits(options),
                file_value, (frame.append_eoc, frame.work_units), crate::recovery::repair_outcome(copied));
        }
        Some(copied?)
    } else {
        None
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(prepared_pdf_input_view);
        reveal(codestream::recovery_framing::framing_outcome);
        reveal(crate::recovery::repair_outcome);
    }
    Ok(PreparedPdfInput {
        file,
        original,
        repaired,
        preflight_work: frame.work_units,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_validate_layout(input@, prepared_pdf_input_view(prepared),
        codestream::complete_codestream_info_view(&layout.info), crate::options::decode_options_limits(options)),
))]
fn validate_pdf_layout(
    input: &[u8],
    prepared: &PreparedPdfInput<'_>,
    layout: &CodestreamLayout<'_>,
    options: &DecodeOptions,
) -> Result<bool, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(prepared_pdf_input_view);
        codestream::complete_codestream_info_known_fields(&layout.info);
    }
    if layout.info.profile.is_part15() {
        return Err(invalid_profile());
    }
    match &prepared.file {
        None => Ok(false),
        Some(file) => Ok(super::pdf_dimensions::validate_header(
            input,
            file,
            &layout.info,
            options.limits(),
        )?
        .ignored_container_dimensions),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_finish_recovery(prepared_pdf_input_view(prepared),
        ignored, selected, trailer, full_canvas_sample_bytes),
))]
fn finish_recovery(
    prepared: &PreparedPdfInput<'_>,
    ignored: bool,
    selected: Option<u16>,
    trailer: u8,
    full_canvas_sample_bytes: Option<u64>,
) -> PdfRecovery {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(prepared_pdf_input_view); }
    let effective = effective_input(prepared).len() as u64;
    PdfRecovery {
        appended_eoc: prepared.repaired.is_some(),
        ignored_container_dimensions: ignored,
        selected_present_tile: selected,
        empty_initial_mq_prefixes: 0,
        discarded_tile_trailer_bytes: u64::from(trailer),
        discarded_pdf_eol_bytes: 0,
        original_codestream_bytes: prepared.original.len() as u64,
        effective_codestream_bytes: effective,
        preflight_work_units: prepared.preflight_work,
        repair_copy_bytes: if prepared.repaired.is_some() {
            effective
        } else {
            0
        },
        full_canvas_sample_bytes,
    }
}

/// Decode raw or single-codestream Part 1 JP2 with explicit PDF recovery.
///
/// Composes the accepted bounded EOC, dimension, sole-present-tile and terminal
/// trailer policies in one call. Genuine pixels/grid, metadata restrictions and
/// limits are retained. Empty initial MQ contributions and deadlines are not
/// silently enabled. Strict APIs are unchanged.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_typed_result(input@, crate::options::decode_selection_view(requested),
        crate::options::decode_options_limits(options), pdf_typed_outcome(result)),
        pdf_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            pdf_typed_outcome(result) == crate::specs::part2_pdf_typed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
fn decode_pdf_compatible_untrimmed(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PdfDecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        reveal(crate::specs::part2_typed_layout);
        crate::specs::part2_pdf_value_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_normal(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let prepared_result = prepare_pdf_input(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = prepared_result {
            crate::specs::part2_pdf_prepare_error(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let prepared = prepared_result?;
    let encoded = effective_input(&prepared);
    let parsed = codestream::parse_layout(encoded, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_pdf_parse_error(input@, crate::options::decode_selection_view(requested),
                crate::options::decode_options_limits(options), prepared_pdf_input_view(&prepared), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(prepared_pdf_input_view);
        codestream::decoder_layout_input_matches_raw(&layout);
        codestream::decoder_layout_input_fields(&layout);
        codestream::decoder_layout_complete_info_matches_raw(&layout);
    }
    let ignored = validate_pdf_layout(input, &prepared, &layout, options)?;
    let chosen = automatic_tile(&layout, requested)?;
    let adjusted = effective_selection(chosen, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    #[cfg(any(not(feature = "pdf-mq-recovery"), verus_keep_ghost))]
    let decoded_result =
        super::pdf_trailers::decode_trailer_layout(&layout, selected, options.limits());
    #[cfg(all(feature = "pdf-mq-recovery", not(verus_keep_ghost)))]
    let ((decoded, trailer), empty_mq_prefixes) = crate::pdf_mq::with_policy(|| {
        super::pdf_trailers::decode_trailer_layout(&layout, selected, options.limits())
    })?;
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Ok(raw) = crate::specs::part1_parse_layout(encoded@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_pdf_decoded_actual(input@, prepared_pdf_input_view(&prepared), raw,
                crate::options::decode_selection_view(requested), ignored, chosen, crate::options::decode_options_limits(options),
                super::pdf_trailers::trailer_layout_outcome(decoded_result));
        }
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost recovered=super::pdf_trailers::trailer_layout_outcome(decoded_result);}
    #[cfg(any(not(feature = "pdf-mq-recovery"), verus_keep_ghost))]
    let (decoded, trailer) = decoded_result?;
    let converted = typed_layout(
        &layout,
        decoded,
        selected.discard_levels(),
        options.limits(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=converted {
            if let Ok(raw)=crate::specs::part1_parse_layout(encoded@,crate::options::decode_options_limits(options)) {
                if let Ok(value)=recovered {
                    crate::specs::part2_pdf_typed_conversion_error(input@,prepared_pdf_input_view(&prepared),raw,
                        crate::options::decode_selection_view(requested),ignored,chosen,crate::options::decode_options_limits(options),value,error);
                }
            }
        }
    }
    let mut image = converted?;
    super::api::validate_part1_output_shape(encoded.len(), &layout, &image)?;
    if let Some(file) = &prepared.file {
        #[cfg(verus_keep_ghost)]
        proof! { jp2::raw_render_file_known(file); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost output_source=crate::image::typed_image_value_view(image);}
        let output = apply_jp2_output(image, file.header(), options.limits());
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error)=output {
                if let Ok(raw)=crate::specs::part1_parse_layout(encoded@,crate::options::decode_options_limits(options)) {
                    if let Ok(value)=recovered {
                        crate::specs::part2_pdf_output_error(input@,prepared_pdf_input_view(&prepared),raw,
                            crate::options::decode_selection_view(requested),ignored,chosen,crate::options::decode_options_limits(options),value,output_source,error);
                    }
                }
            }
        }
        image = output?;
    }
    let report = finish_report(
        &layout.info.image_size,
        requested,
        chosen,
        image.components().len(),
        options.limits(),
    )?;
    let recovery = finish_recovery(
        &prepared,
        ignored,
        chosen,
        trailer.discarded_tile_trailer_bytes,
        report.full_canvas_sample_bytes,
    );
    #[cfg(all(feature = "pdf-mq-recovery", not(verus_keep_ghost)))]
    let recovery = PdfRecovery {
        empty_initial_mq_prefixes: empty_mq_prefixes,
        ..recovery
    };
    Ok(PdfDecodedImage { image, recovery })
}

/// Apply the same PDF policies while retaining centered fractional headroom.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_reconstructed_result(input@, crate::options::decode_selection_view(requested),
        crate::options::decode_options_limits(options), pdf_reconstructed_outcome(result)),
        pdf_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            pdf_reconstructed_outcome(result) == crate::specs::part2_pdf_reconstructed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
fn decode_pdf_reconstructed_untrimmed(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PdfReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_pdf_value_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_normal(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let prepared_result = prepare_pdf_input(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = prepared_result {
            crate::specs::part2_pdf_prepare_error(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let prepared = prepared_result?;
    let encoded = effective_input(&prepared);
    let parsed = codestream::parse_layout(encoded, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_pdf_parse_error(input@, crate::options::decode_selection_view(requested),
                crate::options::decode_options_limits(options), prepared_pdf_input_view(&prepared), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(prepared_pdf_input_view);
        codestream::decoder_layout_input_matches_raw(&layout);
        codestream::decoder_layout_input_fields(&layout);
        codestream::decoder_layout_complete_info_matches_raw(&layout);
    }
    let ignored = validate_pdf_layout(input, &prepared, &layout, options)?;
    let chosen = automatic_tile(&layout, requested)?;
    let adjusted = effective_selection(chosen, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    #[cfg(any(not(feature = "pdf-mq-recovery"), verus_keep_ghost))]
    let decoded_result =
        super::pdf_trailers::decode_trailer_layout(&layout, selected, options.limits());
    #[cfg(all(feature = "pdf-mq-recovery", not(verus_keep_ghost)))]
    let ((image, trailer), empty_mq_prefixes) = crate::pdf_mq::with_policy(|| {
        super::pdf_trailers::decode_trailer_layout(&layout, selected, options.limits())
    })?;
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Ok(raw) = crate::specs::part1_parse_layout(encoded@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_pdf_decoded_actual(input@, prepared_pdf_input_view(&prepared), raw,
                crate::options::decode_selection_view(requested), ignored, chosen, crate::options::decode_options_limits(options),
                super::pdf_trailers::trailer_layout_outcome(decoded_result));
        }
    }
    #[cfg(any(not(feature = "pdf-mq-recovery"), verus_keep_ghost))]
    let (image, trailer) = decoded_result?;
    super::api::validate_reconstruction_transforms(&layout)?;
    super::api::validate_reconstructed_output_shape(encoded.len(), &layout, &image)?;
    if let Some(file) = &prepared.file {
        #[cfg(verus_keep_ghost)]
        proof! { jp2::raw_render_file_known(file); }
        super::api::validate_jp2_reconstruction_output(file.header())?;
        if let Some(association) = file.codestream(0)?.codestream_header() {
            let header = association
                .parsed_header()
                .ok_or(DecodeError::UnsupportedFeature {
                    feature: "unparsed JPX header on reconstruction samples",
                })?;
            super::api::validate_jp2_reconstruction_output(header)?;
        }
    }
    let report = finish_report(
        &layout.info.image_size,
        requested,
        chosen,
        image.components().len(),
        options.limits(),
    )?;
    let recovery = finish_recovery(
        &prepared,
        ignored,
        chosen,
        trailer.discarded_tile_trailer_bytes,
        report.full_canvas_sample_bytes,
    );
    #[cfg(all(feature = "pdf-mq-recovery", not(verus_keep_ghost)))]
    let recovery = PdfRecovery {
        empty_initial_mq_prefixes: empty_mq_prefixes,
        ..recovery
    };
    Ok(PdfReconstructedImage { image, recovery })
}

/// Inspect full SIZ metadata under the same bounded container/EOC admission.
///
/// This parses complete framing and validates non-dimension header declarations;
/// it does not execute packets/entropy or promise that decoding will succeed.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_inspect_result(input@, crate::options::decode_options_limits(options),
        codestream::complete_codestream_info_outcome(result)),
        codestream::complete_codestream_info_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            codestream::complete_codestream_info_outcome(result) == crate::specs::part2_pdf_inspect_value(
                input@, crate::options::decode_options_limits(options)),
))]
fn inspect_pdf_compatible_untrimmed(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<codestream::CodestreamInfo, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        codestream::complete_codestream_info_errors_known();
        let requested = (crate::specs::Part2TileSelection::All, None, 0u8);
        crate::specs::part2_pdf_value_unfold(input@, requested, crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_normal(input@, requested, crate::options::decode_options_limits(options));
    }
    let prepared_result = prepare_pdf_input(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = prepared_result {
            crate::specs::part2_pdf_prepare_error(input@, (crate::specs::Part2TileSelection::All, None, 0u8),
                crate::options::decode_options_limits(options), error);
        }
    }
    let prepared = prepared_result?;
    let encoded = effective_input(&prepared);
    let parsed = codestream::parse_layout(encoded, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_pdf_parse_error(input@, (crate::specs::Part2TileSelection::All, None, 0u8),
                crate::options::decode_options_limits(options), prepared_pdf_input_view(&prepared), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_complete_info_matches_raw(&layout);
        codestream::complete_codestream_info_known_fields(&layout.info);
        if let Ok(raw) = crate::specs::part1_parse_layout(encoded@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_pdf_inspect_actual(input@, prepared_pdf_input_view(&prepared), raw, crate::options::decode_options_limits(options));
        }
    }
    validate_pdf_layout(input, &prepared, &layout, options)?;
    Ok(layout.info)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures pdf_eol_end_outcome(result) == crate::specs::part2_pdf_eol_end(input@, error),
        match result {
        None => crate::specs::part2_pdf_eol_end(input@, error).is_none(),
        Some(end) => crate::specs::part2_pdf_eol_end(input@, error) == Some(end as nat)
            && 2 <= end && end < input.len() && input.len() - end <= 2,
    },
))]
fn pdf_eol_end(input: &[u8], error: DecodeError) -> Option<usize> {
    let offset = match error {
        DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::TrailingData | MalformedKind::InvalidBoxLength,
        } => offset,
        _ => return None,
    };
    if input.len() < 3 {
        return None;
    }
    let count =
        if input.len() >= 4 && input[input.len() - 2] == b'\r' && input[input.len() - 1] == b'\n' {
            2
        } else if input[input.len() - 1] == b'\r' || input[input.len() - 1] == b'\n' {
            1
        } else {
            return None;
        };
    let end = input.len() - count;
    if end < 2 || offset != end as u64 || input[end - 2] != 0xff || input[end - 1] != 0xd9 {
        return None;
    }
    Some(end)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_eol_report(report, count),
))]
fn record_pdf_eol(mut report: PdfRecovery, count: u8) -> PdfRecovery {
    report.discarded_pdf_eol_bytes = count;
    report
}

/// Decode with bounded PDF recoveries, including one reported terminal EOL.
///
/// The original call must first reject exactly at the EOC/EOL boundary.
/// Only LF, CR or CRLF immediately after EOC is eligible; the complete prefix
/// is decoded normally. Strict APIs and all resource limits are unchanged.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_eol_typed_result(input@, crate::options::decode_selection_view(requested),
        crate::options::decode_options_limits(options), pdf_typed_outcome(result)),
        pdf_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            pdf_typed_outcome(result) == crate::specs::part2_pdf_eol_typed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_pdf_compatible(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PdfDecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_contracts_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_eol_contracts_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let first = decode_pdf_compatible_untrimmed(input, options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_eta(
            |events| crate::specs::part2_pdf_typed_run(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events),
            pdf_typed_outcome(first));
    }
    let error = match first {
        Ok(image) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_pdf_eol_passthrough(input@,
                    |bytes, calls| crate::specs::part2_pdf_typed_run(bytes, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls),
                    |value: crate::specs::Part2PdfTyped, count| (value.0, crate::specs::part2_pdf_eol_report(value.1, count)), pdf_typed_outcome(Ok(image)));
            }
            return Ok(image);
        }
        Err(error) => error,
    };
    let end = match pdf_eol_end(input, error) {
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_pdf_eol_passthrough(input@,
                    |bytes, calls| crate::specs::part2_pdf_typed_run(bytes, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls),
                    |value: crate::specs::Part2PdfTyped, count| (value.0, crate::specs::part2_pdf_eol_report(value.1, count)), Err(error));
            }
            return Err(error);
        }
        Some(end) => end,
    };
    let decoded = decode_pdf_compatible_untrimmed(&input[..end], options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_contracts_unfold(input@.take(end as int), crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_decode_eta(
            |events| crate::specs::part2_pdf_typed_run(input@.take(end as int), crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events),
            pdf_typed_outcome(decoded));
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_eol_retried(input@,
            |bytes, calls| crate::specs::part2_pdf_typed_run(bytes, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls),
            |value: crate::specs::Part2PdfTyped, count| (value.0, crate::specs::part2_pdf_eol_report(value.1, count)), error, end as nat, pdf_typed_outcome(decoded));
    }
    let mut image = decoded?;
    image.recovery = record_pdf_eol(image.recovery, (input.len() - end) as u8);
    Ok(image)
}

/// The same PDF EOL policy while preserving centered reconstruction samples.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_eol_reconstructed_result(input@, crate::options::decode_selection_view(requested),
        crate::options::decode_options_limits(options), pdf_reconstructed_outcome(result)),
        pdf_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            pdf_reconstructed_outcome(result) == crate::specs::part2_pdf_eol_reconstructed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_pdf_reconstructed(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PdfReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_contracts_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_eol_contracts_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let first = decode_pdf_reconstructed_untrimmed(input, options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_eta(
            |events| crate::specs::part2_pdf_reconstructed_run(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events),
            pdf_reconstructed_outcome(first));
    }
    let error = match first {
        Ok(image) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_pdf_eol_passthrough(input@,
                    |bytes, calls| crate::specs::part2_pdf_reconstructed_run(bytes, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls),
                    |value: crate::specs::Part2PdfReconstructed, count| (value.0, crate::specs::part2_pdf_eol_report(value.1, count)), pdf_reconstructed_outcome(Ok(image)));
            }
            return Ok(image);
        }
        Err(error) => error,
    };
    let end = match pdf_eol_end(input, error) {
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_pdf_eol_passthrough(input@,
                    |bytes, calls| crate::specs::part2_pdf_reconstructed_run(bytes, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls),
                    |value: crate::specs::Part2PdfReconstructed, count| (value.0, crate::specs::part2_pdf_eol_report(value.1, count)), Err(error));
            }
            return Err(error);
        }
        Some(end) => end,
    };
    let decoded = decode_pdf_reconstructed_untrimmed(&input[..end], options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_contracts_unfold(input@.take(end as int), crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_decode_eta(
            |events| crate::specs::part2_pdf_reconstructed_run(input@.take(end as int), crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events),
            pdf_reconstructed_outcome(decoded));
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_eol_retried(input@,
            |bytes, calls| crate::specs::part2_pdf_reconstructed_run(bytes, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls),
            |value: crate::specs::Part2PdfReconstructed, count| (value.0, crate::specs::part2_pdf_eol_report(value.1, count)), error, end as nat, pdf_reconstructed_outcome(decoded));
    }
    let mut image = decoded?;
    image.recovery = record_pdf_eol(image.recovery, (input.len() - end) as u8);
    Ok(image)
}

/// Inspect with the same original-error-gated PDF EOL policy as decoding.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_eol_inspect_result(input@, crate::options::decode_options_limits(options),
        codestream::complete_codestream_info_outcome(result)),
        codestream::complete_codestream_info_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            codestream::complete_codestream_info_outcome(result) == crate::specs::part2_pdf_eol_inspect_value(
                input@, crate::options::decode_options_limits(options)),
))]
pub fn inspect_pdf_compatible(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<codestream::CodestreamInfo, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::complete_codestream_info_errors_known();
        crate::specs::part2_pdf_contracts_unfold(input@, (crate::specs::Part2TileSelection::All, None, 0u8), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_eol_contracts_unfold(input@, (crate::specs::Part2TileSelection::All, None, 0u8), crate::options::decode_options_limits(options));
    }
    let first = inspect_pdf_compatible_untrimmed(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_eta(
            |events| crate::specs::part2_pdf_inspect_run(input@, crate::options::decode_options_limits(options), events),
            codestream::complete_codestream_info_outcome(first));
    }
    let error = match first {
        Ok(info) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                codestream::complete_codestream_info_known_fields(&info);
                crate::specs::part2_pdf_eol_passthrough(input@,
                    |bytes, calls| crate::specs::part2_pdf_inspect_run(bytes, crate::options::decode_options_limits(options), calls),
                    |value: crate::specs::Part2RawCodestreamInfo, _count| value, codestream::complete_codestream_info_outcome(Ok(info)));
            }
            return Ok(info);
        }
        Err(error) => error,
    };
    let end = match pdf_eol_end(input, error) {
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_pdf_eol_passthrough(input@,
                    |bytes, calls| crate::specs::part2_pdf_inspect_run(bytes, crate::options::decode_options_limits(options), calls),
                    |value: crate::specs::Part2RawCodestreamInfo, _count| value, Err(error));
            }
            return Err(error);
        }
        Some(end) => end,
    };
    let inspected = inspect_pdf_compatible_untrimmed(&input[..end], options);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_contracts_unfold(input@.take(end as int), (crate::specs::Part2TileSelection::All, None, 0u8), crate::options::decode_options_limits(options));
        crate::specs::part2_decode_eta(
            |events| crate::specs::part2_pdf_inspect_run(input@.take(end as int), crate::options::decode_options_limits(options), events),
            codestream::complete_codestream_info_outcome(inspected));
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_eol_retried(input@,
            |bytes, calls| crate::specs::part2_pdf_inspect_run(bytes, crate::options::decode_options_limits(options), calls),
            |value: crate::specs::Part2RawCodestreamInfo, _count| value, error, end as nat, codestream::complete_codestream_info_outcome(inspected));
    }
    inspected
}
