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
    /// TNsot fields corrected after complete sequential per-tile framing.
    pub corrected_tile_part_count_fields: u32,
    pub tile_part_count_repair_copy_bytes: u64,
    /// Conservative charged bound for framing, scratch initialization and copy.
    pub tile_part_count_repair_work_bound: u64,
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
    ordinary: bool,
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
            ordinary: value.ordinary,
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
    ensures result == crate::specs::part2_pdf_ht_announcement(input@),
))]
fn ht_announcement(input: &[u8]) -> bool {
    input.len() >= 8
        && input[0] == 0xff
        && input[1] == 0x4f
        && input[2] == 0xff
        && input[3] == 0x51
        && input[6] & 0x40 != 0
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_file_is_jpx(jp2::raw_jp2_file_view(file)),
))]
fn jpx_file(file: &jp2::Jp2File<'_>) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! {
        jp2::raw_render_file_known(file);
        reveal(crate::specs::part2_pdf_file_is_jpx);
    }
    file.file_type().is_jpx_compatible()
        && !file.file_type().is_jp2_primary()
        && !file.file_type().is_jph_compatible()
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Err(error) => crate::specs::part2_pdf_output_header(prepared_pdf_input_view(prepared)) == Err(error),
        Ok(header) => crate::specs::part2_pdf_output_header(prepared_pdf_input_view(prepared))
            == Ok(jp2::associated_header_option(header)),
    },
))]
fn output_header<'p>(
    prepared: &'p PreparedPdfInput<'_>,
) -> Result<Option<&'p jp2::Jp2Header>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(prepared_pdf_input_view);
        reveal(crate::specs::part2_pdf_output_header);
        reveal(crate::specs::part2_jpx_cold_header);
    }
    match &prepared.file {
        None => Ok(None),
        Some(file) => {
            #[cfg(verus_keep_ghost)]
            proof! { jp2::raw_render_file_known(file); }
            if jpx_file(file) {
                let source = file.codestream(0)?;
                #[cfg(verus_keep_ghost)]
                proof! { jp2::codestream_source_known_fields(source); }
                Ok(Some(jp2::associated_header_for_codestream(
                    source,
                    file.header(),
                )?))
            } else {
                Ok(Some(file.header()))
            }
        }
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
        let legacy = kind.is_compatible_with(jp2::BoxType::JP2_BRAND)
            && (!kind.is_jpx_compatible() || kind.is_jp2_primary())
            && !kind.is_jph_compatible();
        let jph = kind.is_jph_primary() && kind.is_jph_compatible() && !kind.is_jpx_compatible();
        let jpx = jpx_file(&file);
        if (!legacy && !jph && !jpx) || file.codestream_count() != 1 {
            return Err(invalid_profile());
        }
        if jpx {
            jp2::validate_pdf_jpx(input, &file, options.limits())?;
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
    let ordinary = ht_announcement(original)
        || match &file {
            None => false,
            Some(file) => file.file_type().is_jph_compatible() || jpx_file(file),
        };
    if ordinary {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_pdf_prepare_ordinary_actual(
                input@, crate::options::decode_options_limits(options), file_value);
            reveal(prepared_pdf_input_view);
        }
        return Ok(PreparedPdfInput {
            file,
            original,
            repaired: None,
            preflight_work: 0,
            ordinary,
        });
    }
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
        ordinary,
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
    let jpx = match &prepared.file {
        None => false,
        Some(file) => jpx_file(file),
    };
    if layout.info.profile.is_part15() != (prepared.ordinary && !jpx) {
        return Err(invalid_profile());
    }
    match &prepared.file {
        None => Ok(false),
        Some(file) => {
            if jpx {
                let source = file.codestream(0)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    jp2::raw_render_file_known(file);
                    jp2::codestream_source_known_fields(source);
                    reveal(crate::specs::part2_jpx_cold_header);
                    reveal(crate::specs::part2_jpx_cold_validate);
                }
                let header = jp2::associated_header_for_codestream(source, file.header())?;
                jp2::validate_selected_header(header, &layout.info, source.box_header().offset())?;
                return Ok(false);
            }
            let ignored = super::pdf_dimensions::validate_header(
                input,
                file,
                &layout.info,
                options.limits(),
            )?
            .ignored_container_dimensions;
            if prepared.ordinary && ignored {
                return Err(DecodeError::malformed(
                    0,
                    MalformedKind::ContainerCodestreamMismatch,
                ));
            }
            Ok(ignored)
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_layout_result(
        codestream::decoder_layout_input_view(layout), crate::options::decode_selection_view(selected),
        limits, ordinary, super::pdf_trailers::trailer_layout_outcome(result)),
        super::pdf_trailers::trailer_layout_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            super::pdf_trailers::trailer_layout_outcome(result) == crate::specs::part2_pdf_layout_value(
                codestream::decoder_layout_input_view(layout), crate::options::decode_selection_view(selected),
                limits, ordinary),
))]
fn decode_pdf_layout(
    layout: &CodestreamLayout<'_>,
    selected: &DecodeSelection,
    limits: &ResourceLimits,
    ordinary: bool,
) -> Result<(DecodedImage, super::pdf_trailers::TileTrailerRecoveryReport), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_input_fields(layout);
        reveal(crate::specs::part2_pdf_layout_result);
        reveal(crate::specs::part2_pdf_layout_value);
        reveal(crate::specs::part2_decode_layout_selected);
    }
    if ordinary {
        let decoded = super::execution::decode_layout_selected(layout, selected, limits);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_pdf_layout_ordinary_actual(
                codestream::decoder_layout_input_view(layout),
                crate::options::decode_selection_view(selected), limits,
                crate::image::decoded_image_outcome(decoded));
        }
        let image = decoded?;
        Ok((
            image,
            super::pdf_trailers::TileTrailerRecoveryReport {
                discarded_tile_trailer_bytes: 0,
            },
        ))
    } else {
        let decoded = super::pdf_trailers::decode_trailer_layout(layout, selected, limits);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_pdf_layout_trailer_actual(
                codestream::decoder_layout_input_view(layout),
                crate::options::decode_selection_view(selected), limits,
                super::pdf_trailers::trailer_layout_outcome(decoded));
        }
        decoded
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
        corrected_tile_part_count_fields: 0,
        tile_part_count_repair_copy_bytes: 0,
        tile_part_count_repair_work_bound: 0,
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
    let chosen = if prepared.ordinary {
        None
    } else {
        automatic_tile(&layout, requested)?
    };
    let adjusted = effective_selection(chosen, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    #[cfg(any(not(feature = "pdf-mq-recovery"), verus_keep_ghost))]
    let decoded_result = decode_pdf_layout(&layout, selected, options.limits(), prepared.ordinary);
    #[cfg(all(feature = "pdf-mq-recovery", not(verus_keep_ghost)))]
    let ((decoded, trailer), empty_mq_prefixes) = if prepared.ordinary {
        (
            decode_pdf_layout(&layout, selected, options.limits(), true)?,
            0,
        )
    } else {
        crate::pdf_mq::with_policy(|| {
            decode_pdf_layout(&layout, selected, options.limits(), false)
        })?
    };
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
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_output_header_admitted(
            input@, prepared_pdf_input_view(&prepared),
            codestream::complete_codestream_info_view(&layout.info),
            crate::options::decode_options_limits(options));
    }
    let selected_header = output_header(&prepared)?;
    if let Some(header) = selected_header {
        #[cfg(verus_keep_ghost)]
        proof! { jp2::raw_render_header_known(header); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost output_source=crate::image::typed_image_value_view(image);}
        let output = apply_jp2_output(image, header, options.limits());
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
    let chosen = if prepared.ordinary {
        None
    } else {
        automatic_tile(&layout, requested)?
    };
    let adjusted = effective_selection(chosen, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    #[cfg(any(not(feature = "pdf-mq-recovery"), verus_keep_ghost))]
    let decoded_result = decode_pdf_layout(&layout, selected, options.limits(), prepared.ordinary);
    #[cfg(all(feature = "pdf-mq-recovery", not(verus_keep_ghost)))]
    let ((image, trailer), empty_mq_prefixes) = if prepared.ordinary {
        (
            decode_pdf_layout(&layout, selected, options.limits(), true)?,
            0,
        )
    } else {
        crate::pdf_mq::with_policy(|| {
            decode_pdf_layout(&layout, selected, options.limits(), false)
        })?
    };
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
fn decode_pdf_eol_compatible(
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
fn decode_pdf_eol_reconstructed(
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
fn inspect_pdf_eol_compatible(
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_count_prepared_base(prepared_pdf_input_view(prepared), error),
))]
fn count_repair_base(
    prepared: &PreparedPdfInput<'_>,
    error: DecodeError,
) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(prepared_pdf_input_view); }
    if prepared.repaired.is_some() || prepared.ordinary {
        return Err(error);
    }
    match &prepared.file {
        None => Ok(0),
        Some(file) => {
            #[cfg(verus_keep_ghost)]
            proof! { jp2::raw_render_file_known(file); }
            if !file.file_type().is_jp2_primary() || file.codestream_count() != 1 {
                return Err(error);
            }
            let source = file.codestream(0)?;
            let header = source.box_header();
            let base = header.payload_offset()?;
            usize::try_from(base).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError => ensures result == error,))]
                |_failure| error,
            )
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_count_prepare_result(input@,
        crate::options::decode_options_limits(options), error, crate::pdf_tile_count::count_repair_outcome(result)),
        crate::pdf_tile_count::count_repair_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            crate::pdf_tile_count::count_repair_outcome(result) == crate::specs::part2_count_prepare_value(input@,
                crate::options::decode_options_limits(options), error),
))]
fn prepare_pdf_count_repair(
    input: &[u8],
    options: &DecodeOptions,
    error: DecodeError,
) -> Result<crate::pdf_tile_count::PdfCountRepair, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_count_prepare_value_unfold(input@,
            crate::options::decode_options_limits(options), error);
    }
    let admitted = crate::pdf_tile_count::admit_input(input.len(), options.limits(), error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = admitted {
            crate::specs::part2_count_prepare_admission_error(input@,
                crate::options::decode_options_limits(options), error, failure);
        }
    }
    let _offset = admitted?;
    let prepared = prepare_pdf_input(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = prepared {
            crate::specs::part2_count_prepare_lift(input@,
                crate::options::decode_options_limits(options), error, _offset,
                prepared_pdf_input_outcome(prepared), Err(failure));
        }
    }
    let prepared = prepared?;
    let base = count_repair_base(&prepared, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = base {
            crate::specs::part2_count_prepare_lift(input@,
                crate::options::decode_options_limits(options), error, _offset,
                Ok(prepared_pdf_input_view(&prepared)), Err(failure));
        }
    }
    let base = base?;
    let repaired = crate::pdf_tile_count::recover_pdf_tile_part_counts(
        input,
        prepared.original,
        base,
        options,
        error,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_count_prepare_lift(input@,
            crate::options::decode_options_limits(options), error, _offset,
            Ok(prepared_pdf_input_view(&prepared)), crate::pdf_tile_count::count_repair_outcome(repaired));
    }
    repaired
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_count_report(report, fields, bytes, work),
))]
fn record_pdf_counts(mut report: PdfRecovery, fields: u32, bytes: u64, work: u64) -> PdfRecovery {
    report.corrected_tile_part_count_fields = fields;
    report.tile_part_count_repair_copy_bytes = bytes;
    report.tile_part_count_repair_work_bound = work;
    report
}

/// Compose the explicit PDF policies, including complete off-by-one TNsot recovery.
///
/// Strict entry points retain their original rejection. A count correction
/// requires complete per-tile sequences, a uniform declaration and the actual
/// failing SOT offset; the repaired input is parsed and decoded normally.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_count_typed_result(input@, crate::options::decode_selection_view(requested),
        crate::options::decode_options_limits(options), pdf_typed_outcome(result)),
        pdf_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            pdf_typed_outcome(result) == crate::specs::part2_pdf_count_typed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_pdf_compatible(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PdfDecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost base = |bytes, calls| crate::specs::part2_pdf_eol_typed_run(bytes,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls);
        let ghost finish = |value, repaired| crate::specs::part2_count_finish_typed(value, repaired);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_eol_frames(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_count_contracts_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let first = decode_pdf_eol_compatible(input, options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_eta(|events| crate::specs::part2_pdf_eol_typed_run(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events), pdf_typed_outcome(first));
    }
    let error = match first {
        Err(
            error @ DecodeError::MalformedInput {
                kind: MalformedKind::InvalidTilePart,
                ..
            },
        ) => error,
        other => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_count_passthrough(input@, crate::options::decode_options_limits(options),
                    base, finish, pdf_typed_outcome(other));
            }
            return other;
        }
    };
    let repaired = prepare_pdf_count_repair(input, options, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = repaired {
            crate::specs::part2_count_retried(input@, crate::options::decode_options_limits(options),
                base, finish, error, Err(failure), Err(failure));
        }
    }
    let repaired = repaired?;
    let decoded = decode_pdf_eol_compatible(&repaired.bytes, options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        let repaired_value = (repaired.bytes@, repaired.fields, repaired.work_units);
        crate::specs::part2_pdf_eol_frames(repaired.bytes@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_decode_eta(|events| crate::specs::part2_pdf_eol_typed_run(repaired.bytes@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events), pdf_typed_outcome(decoded));
        crate::specs::part2_count_finished(repaired_value, base, finish, pdf_typed_outcome(decoded));
        crate::specs::part2_count_retried(input@, crate::options::decode_options_limits(options),
            base, finish, error, Ok(repaired_value), crate::specs::part2_count_reply(pdf_typed_outcome(decoded), repaired_value, finish));
    }
    let mut decoded = decoded?;
    decoded.recovery = record_pdf_counts(
        decoded.recovery,
        repaired.fields,
        repaired.bytes.len() as u64,
        repaired.work_units,
    );
    Ok(decoded)
}

/// The same reported count correction while retaining centered sample headroom.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_count_reconstructed_result(input@, crate::options::decode_selection_view(requested),
        crate::options::decode_options_limits(options), pdf_reconstructed_outcome(result)),
        pdf_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            pdf_reconstructed_outcome(result) == crate::specs::part2_pdf_count_reconstructed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_pdf_reconstructed(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PdfReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost base = |bytes, calls| crate::specs::part2_pdf_eol_reconstructed_run(bytes,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), calls);
        let ghost finish = |value, repaired| crate::specs::part2_count_finish_reconstructed(value, repaired);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_pdf_eol_frames(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_count_contracts_unfold(input@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let first = decode_pdf_eol_reconstructed(input, options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_eta(|events| crate::specs::part2_pdf_eol_reconstructed_run(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events), pdf_reconstructed_outcome(first));
    }
    let error = match first {
        Err(
            error @ DecodeError::MalformedInput {
                kind: MalformedKind::InvalidTilePart,
                ..
            },
        ) => error,
        other => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_count_passthrough(input@, crate::options::decode_options_limits(options),
                    base, finish, pdf_reconstructed_outcome(other));
            }
            return other;
        }
    };
    let repaired = prepare_pdf_count_repair(input, options, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = repaired {
            crate::specs::part2_count_retried(input@, crate::options::decode_options_limits(options),
                base, finish, error, Err(failure), Err(failure));
        }
    }
    let repaired = repaired?;
    let decoded = decode_pdf_eol_reconstructed(&repaired.bytes, options, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        let repaired_value = (repaired.bytes@, repaired.fields, repaired.work_units);
        crate::specs::part2_pdf_eol_frames(repaired.bytes@, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_decode_eta(|events| crate::specs::part2_pdf_eol_reconstructed_run(repaired.bytes@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), events), pdf_reconstructed_outcome(decoded));
        crate::specs::part2_count_finished(repaired_value, base, finish, pdf_reconstructed_outcome(decoded));
        crate::specs::part2_count_retried(input@, crate::options::decode_options_limits(options),
            base, finish, error, Ok(repaired_value), crate::specs::part2_count_reply(pdf_reconstructed_outcome(decoded), repaired_value, finish));
    }
    let mut decoded = decoded?;
    decoded.recovery = record_pdf_counts(
        decoded.recovery,
        repaired.fields,
        repaired.bytes.len() as u64,
        repaired.work_units,
    );
    Ok(decoded)
}

/// Inspect with the same bounded count and EOL admission as PDF decoding.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_pdf_count_inspect_result(input@, crate::options::decode_options_limits(options),
        codestream::complete_codestream_info_outcome(result)),
        codestream::complete_codestream_info_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            codestream::complete_codestream_info_outcome(result) == crate::specs::part2_pdf_count_inspect_value(
                input@, crate::options::decode_options_limits(options)),
))]
pub fn inspect_pdf_compatible(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<codestream::CodestreamInfo, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost base = |bytes, calls| crate::specs::part2_pdf_eol_inspect_run(bytes, crate::options::decode_options_limits(options), calls);
        let ghost finish = |value: crate::specs::Part2RawCodestreamInfo, _repaired| value;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::complete_codestream_info_errors_known();
        crate::specs::part2_pdf_eol_frames(input@, (crate::specs::Part2TileSelection::All, None, 0u8), crate::options::decode_options_limits(options));
        crate::specs::part2_pdf_count_contracts_unfold(input@, (crate::specs::Part2TileSelection::All, None, 0u8), crate::options::decode_options_limits(options));
    }
    let first = inspect_pdf_eol_compatible(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_eta(|events| crate::specs::part2_pdf_eol_inspect_run(input@,
            crate::options::decode_options_limits(options), events), codestream::complete_codestream_info_outcome(first));
    }
    let error = match first {
        Err(
            error @ DecodeError::MalformedInput {
                kind: MalformedKind::InvalidTilePart,
                ..
            },
        ) => error,
        other => {
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Ok(info) = other { codestream::complete_codestream_info_known_fields(&info); }
                crate::specs::part2_count_passthrough(input@, crate::options::decode_options_limits(options),
                    base, finish, codestream::complete_codestream_info_outcome(other));
            }
            return other;
        }
    };
    let repaired = prepare_pdf_count_repair(input, options, error);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(failure) = repaired {
            crate::specs::part2_count_retried(input@, crate::options::decode_options_limits(options),
                base, finish, error, Err(failure), Err(failure));
        }
    }
    let repaired = repaired?;
    let inspected = inspect_pdf_eol_compatible(&repaired.bytes, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        let repaired_value = (repaired.bytes@, repaired.fields, repaired.work_units);
        crate::specs::part2_pdf_eol_frames(repaired.bytes@, (crate::specs::Part2TileSelection::All, None, 0u8), crate::options::decode_options_limits(options));
        crate::specs::part2_decode_eta(|events| crate::specs::part2_pdf_eol_inspect_run(repaired.bytes@,
            crate::options::decode_options_limits(options), events), codestream::complete_codestream_info_outcome(inspected));
        crate::specs::part2_count_finished(repaired_value, base, finish, codestream::complete_codestream_info_outcome(inspected));
        crate::specs::part2_count_retried(input@, crate::options::decode_options_limits(options),
            base, finish, error, Ok(repaired_value), codestream::complete_codestream_info_outcome(inspected));
    }
    inspected
}
