use super::{DecodedImage, TypedImage, apply_jp2_output, arithmetic_overflow, codestream, jp2};
use crate::{DecodeError, DecodeOptions, MalformedKind, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The dimensions selected for one explicitly recovered JP2 codestream.
///
/// `width`, `height` and origins describe the genuine SIZ canvas, not decoded
/// pixels promised by inspection. A later decode may still reject missing tiles
/// or malformed entropy. Header dimensions are retained without relabeling data.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct Jp2DimensionRecoveryReport {
    pub ignored_container_dimensions: bool,
    pub header_width: u32,
    pub header_height: u32,
    pub width: u32,
    pub height: u32,
    pub x_origin: u32,
    pub y_origin: u32,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct Jp2DimensionInspection<'a> {
    pub file: jp2::Jp2File<'a>,
    pub codestream: codestream::CodestreamInfo,
    pub report: Jp2DimensionRecoveryReport,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct Jp2DimensionRecoveredImage {
    pub image: TypedImage,
    pub report: Jp2DimensionRecoveryReport,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct Jp2DimensionRecoveredReconstructedImage {
    pub image: DecodedImage,
    pub report: Jp2DimensionRecoveryReport,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn dimension_inspection_view(value: &Jp2DimensionInspection)
        -> crate::specs::Part2DimensionInspection {
        (jp2::raw_jp2_file_view(&value.file),
            codestream::complete_codestream_info_view(&value.codestream), value.report)
    }

    pub open spec fn dimension_inspection_outcome(
        result: Result<Jp2DimensionInspection, DecodeError>,
    ) -> Result<crate::specs::Part2DimensionInspection, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) => Ok(dimension_inspection_view(&value)) }
    }

    pub open spec fn dimension_typed_outcome(
        result: Result<Jp2DimensionRecoveredImage, DecodeError>,
    ) -> Result<(crate::specs::Part1DecodedTypedImage, Jp2DimensionRecoveryReport), DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok(value) => Ok((crate::image::typed_image_value_view(value.image), value.report)),
        }
    }

    pub open spec fn dimension_reconstructed_outcome(
        result: Result<Jp2DimensionRecoveredReconstructedImage, DecodeError>,
    ) -> Result<(crate::specs::Part1DecodedImageModel, Jp2DimensionRecoveryReport), DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok(value) => Ok((crate::image::decoded_image_view(value.image), value.report)),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_dimension_mismatch(offset),
))]
fn mismatch(offset: u64) -> DecodeError {
    DecodeError::malformed(offset, MalformedKind::ContainerCodestreamMismatch)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures jp2::box_read_outcome(result)
        == crate::specs::part2_dimension_find_box(input@, wanted, limits),
))]
fn find_box<'a>(
    input: &'a [u8],
    wanted: jp2::BoxType,
    limits: &ResourceLimits,
) -> Result<Option<jp2::BoxRef<'a>>, DecodeError> {
    let mut reader = jp2::BoxReader::new(input, limits)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_dimension_find_box);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant jp2::box_reader_state(&reader).input == input@,
            jp2::box_reader_state(&reader).position <= input.len(),
            crate::specs::part2_dimension_find_box(input@, wanted, limits)
                == crate::specs::part2_dimension_find_box_from(jp2::box_reader_state(&reader), wanted),
        decreases input.len() - jp2::box_reader_state(&reader).position,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = jp2::box_reader_state(&reader); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_dimension_find_box_from, 1);
            crate::specs::part2_dimension_box_progress(before);
        }
        let Some(next) = reader.next_box_ref() else {
            return Ok(None);
        };
        let item = next?;
        if item.header.box_type().equals(wanted) {
            return Ok(Some(item));
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_dimension_precision(
        bytes@, codestream::parsed_image_size_view(size), offset),
))]
fn validate_variable_precision(
    bytes: &[u8],
    size: &codestream::ImageSize,
    offset: u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::parsed_image_size_known_fields(size); }
    if bytes.len() != usize::from(size.components) {
        return Err(mismatch(offset));
    }
    let mut index = 0_u16;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index as nat <= bytes.len(), bytes.len() == size.components,
            codestream::parsed_image_size_view(size).components == size.components,
            codestream::parsed_image_size_view(size).infos == codestream::image_size_component_infos(size),
            codestream::image_size_component_count(size) == size.components,
            crate::specs::part2_dimension_precision(bytes@, codestream::parsed_image_size_view(size), offset)
                == crate::specs::part2_dimension_precision_from(bytes@, codestream::parsed_image_size_view(size), offset, index as nat),
        decreases bytes.len() - index,
    ))]
    while usize::from(index) < bytes.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_dimension_precision_from, 1); }
        let component = size.component(index)?;
        let byte = bytes[usize::from(index)];
        if u16::from(byte % 128) + 1 != u16::from(component.precision)
            || (byte >= 128) != component.signed
        {
            return Err(mismatch(offset));
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_dimension_precision_from, 1); }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_dimension_validate_header(
        input@, jp2::raw_jp2_file_view(file),
        codestream::complete_codestream_info_view(info), limits),
))]
fn validate_header(
    input: &[u8],
    file: &jp2::Jp2File<'_>,
    info: &codestream::CodestreamInfo,
    limits: &ResourceLimits,
) -> Result<Jp2DimensionRecoveryReport, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::complete_codestream_info_known_fields(info);
        jp2::raw_render_file_known(file);
    }
    let stream = file.codestream(0)?;
    let offset = stream.box_header().offset();
    let association = stream.codestream_header();
    let header = match association {
        None => file.header(),
        Some(association) => {
            association
                .parsed_header()
                .ok_or(DecodeError::UnsupportedFeature {
                    feature: "unparsed JPX header in dimension recovery",
                })?
        }
    };
    jp2::validate_container_image_header(
        jp2::ImageHeader {
            width: info.image_size.width,
            height: info.image_size.height,
            ..header.image
        },
        info,
        offset,
    )?;
    if matches!(header.image.bit_depth, jp2::ComponentBitDepth::Variable) {
        let main = find_box(input, jp2::BoxType::JP2_HEADER, limits)?.ok_or(mismatch(offset))?;
        let inherited = find_box(main.payload, jp2::BoxType::BITS_PER_COMPONENT, limits)?;
        let selected = match association {
            None => inherited,
            Some(association) => match find_box(
                association.payload(),
                jp2::BoxType::BITS_PER_COMPONENT,
                limits,
            )? {
                Some(found) => Some(found),
                None => inherited,
            },
        };
        let depths = selected.ok_or(mismatch(offset))?;
        validate_variable_precision(depths.payload, &info.image_size, offset)?;
    }
    // ImageSize already stores the extent after the reference-grid origin.
    let width = info.image_size.width;
    let height = info.image_size.height;
    Ok(Jp2DimensionRecoveryReport {
        ignored_container_dimensions: header.image.width != width || header.image.height != height,
        header_width: header.image.width,
        header_height: header.image.height,
        width,
        height,
        x_origin: info.image_size.x_origin,
        y_origin: info.image_size.y_origin,
    })
}

/// Inspect JP2 while explicitly accepting contradictory container dimensions.
///
/// All framing, profile, component count, precision/sign and resource checks
/// remain. Variable BPCC declarations are compared with every SIZ component.
/// Inspection does not execute entropy decoding or promise a decoded image.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_dimension_inspection_result(
        input@, crate::options::decode_options_limits(options), dimension_inspection_outcome(result)),
        dimension_inspection_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            dimension_inspection_outcome(result) == crate::specs::part2_dimension_inspection_value(
                input@, crate::options::decode_options_limits(options)),
        match result { Err(_) => true, Ok(value) => jp2::raw_jp2_file_view(&value.file).streams.len() > 0 },
))]
pub fn inspect_jp2_recover_dimensions<'a>(
    input: &'a [u8],
    options: &DecodeOptions,
) -> Result<Jp2DimensionInspection<'a>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_dimension_inspection_value_unfold(input@, crate::options::decode_options_limits(options));
        crate::specs::part2_dimension_inspection_normal(input@, crate::options::decode_options_limits(options));
        codestream::complete_codestream_info_errors_known();
    }
    let parsed_file = jp2::parse(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed_file {
            crate::specs::part2_dimension_inspection_pure_error(
                input@, crate::options::decode_options_limits(options), error);
        }
    }
    let file = parsed_file?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(&file); }
    let selected = file.codestream(0);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = selected {
            crate::specs::part2_dimension_inspection_pure_error(
                input@, crate::options::decode_options_limits(options), error);
        }
    }
    let stream = selected?;
    let parsed_info = codestream::parse(stream.data(), options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_dimension_inspection_info_actual(input@, jp2::raw_jp2_file_view(&file),
            crate::options::decode_options_limits(options), codestream::complete_codestream_info_outcome(parsed_info));
    }
    let info = parsed_info?;
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::complete_codestream_info_known_fields(&info);
        jp2::raw_render_file_known(&file);
    }
    if file.file_type().is_jph_compatible() != info.profile.is_part15() {
        return Err(DecodeError::malformed(
            stream.box_header().offset(),
            MalformedKind::InvalidProfile,
        ));
    }
    let report = validate_header(input, &file, &info, options.limits())?;
    super::api::validate_jp2_display_profile(&file)?;
    Ok(Jp2DimensionInspection {
        file,
        codestream: info,
        report,
    })
}

/// Decode JP2 using genuine SIZ dimensions instead of contradictory IHDR sizes.
///
/// This opts into dimension recovery only: strict APIs remain strict, no EOC is
/// appended, no absent tile is synthesized, and typed palette/channel/NLT work
/// is preserved. The report retains the original declaration and actual canvas.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_dimension_typed_result(
        input@, crate::options::decode_options_limits(options), dimension_typed_outcome(result)),
        dimension_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            dimension_typed_outcome(result) == crate::specs::part2_dimension_typed_value(
                input@, crate::options::decode_options_limits(options)),
))]
pub fn decode_jp2_recover_dimensions(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<Jp2DimensionRecoveredImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_dimension_decode_value_unfold(input@, crate::options::decode_options_limits(options));
        crate::specs::part2_dimension_decode_normal(input@, crate::options::decode_options_limits(options));
    }
    let inspected_result = inspect_jp2_recover_dimensions(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = inspected_result {
            crate::specs::part2_dimension_decode_inspection_error(
                input@, crate::options::decode_options_limits(options), error);
        }
    }
    let inspected = inspected_result?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(&inspected.file); }
    let decoded_result = super::decode_codestream(inspected.file.codestream(0)?.data(), options);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_dimension_typed_actual(input@, crate::options::decode_options_limits(options),
            dimension_inspection_view(&inspected), crate::image::decoded_typed_image_outcome(decoded_result));
    }
    let decoded = decoded_result?;
    let image = apply_jp2_output(decoded, inspected.file.header(), options.limits())?;
    Ok(Jp2DimensionRecoveredImage {
        image,
        report: inspected.report,
    })
}

/// Recover JP2 dimensions while retaining centered samples for interpolation.
///
/// Main/associated palette/channel processing and NLT are rejected exactly as
/// with `decode_jp2_reconstructed`; genuine decoding errors are never retried.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_dimension_reconstructed_result(
        input@, crate::options::decode_options_limits(options), dimension_reconstructed_outcome(result)),
        dimension_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            dimension_reconstructed_outcome(result) == crate::specs::part2_dimension_reconstructed_value(
                input@, crate::options::decode_options_limits(options)),
))]
pub fn decode_jp2_reconstructed_recover_dimensions(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<Jp2DimensionRecoveredReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_dimension_decode_value_unfold(input@, crate::options::decode_options_limits(options));
        crate::specs::part2_dimension_decode_normal(input@, crate::options::decode_options_limits(options));
    }
    let inspected_result = inspect_jp2_recover_dimensions(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = inspected_result {
            crate::specs::part2_dimension_decode_inspection_error(
                input@, crate::options::decode_options_limits(options), error);
        }
    }
    let inspected = inspected_result?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(&inspected.file); }
    let stream = inspected.file.codestream(0)?;
    let decoded_result = super::decode_codestream_reconstructed(stream.data(), options);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_dimension_reconstructed_actual(input@, crate::options::decode_options_limits(options),
            dimension_inspection_view(&inspected), crate::image::decoded_image_outcome(decoded_result));
    }
    let image = decoded_result?;
    super::api::validate_jp2_reconstruction_output(inspected.file.header())?;
    if let Some(association) = stream.codestream_header() {
        let header = association
            .parsed_header()
            .ok_or(DecodeError::UnsupportedFeature {
                feature: "unparsed JPX header on reconstruction samples",
            })?;
        super::api::validate_jp2_reconstruction_output(header)?;
    }
    Ok(Jp2DimensionRecoveredReconstructedImage {
        image,
        report: inspected.report,
    })
}
