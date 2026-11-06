//! Container assembly, file profiles, and codestream inspection.

use super::{
    BoxHeader, BoxReader, BoxRef, BoxType, CodestreamBox, CodestreamHeaderAssociation,
    CodestreamInfo, ComponentBitDepth, CompositingLayer, Composition, DecodeError, FileType,
    InspectedJp2, Jp2File, Jp2Header, MalformedKind, Resource, ResourceLimits, SIGNATURE_MAGIC,
    codestream, inspect_metadata_box, parse_codestream_header, parse_compositing_layer,
    parse_composition, parse_jp2_header, read_box_type_at, read_u32, required_box,
    validate_layer_references,
};
#[cfg(verus_keep_ghost)]
use super::{
    associated_header_outcome, associated_header_view, codestream_header_association_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl FileType {
    pub fn compatible_brands(&self) -> &[BoxType] {
        &self.compatible_brands
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_file_type_compatible(super::file_type_view(self), brand),
    ))]
    pub fn is_compatible_with(&self, brand: BoxType) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(super::file_type_view); }
        if self.brand.equals(brand) {
            return true;
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.compatible_brands.len(),
                    self.brand != brand,
                    forall|i: int| 0 <= i < index ==> self.compatible_brands@[i] != brand,
                decreases self.compatible_brands.len() - index,
            )
        )]
        while index < self.compatible_brands.len() {
            let compatible = match self.compatible_brands.get(index) {
                Some(value) => value,
                None => return false,
            };
            if compatible.equals(brand) {
                return true;
            }
            index += 1;
        }
        false
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_file_type_jpx(super::file_type_view(self)),
    ))]
    pub fn is_jpx_compatible(&self) -> bool {
        self.is_compatible_with(BoxType::JPX_BRAND)
            || self.is_compatible_with(BoxType::JPX_BASELINE_BRAND)
    }

    pub fn is_jph_compatible(&self) -> bool {
        self.is_compatible_with(BoxType::JPH_BRAND)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures associated_header_outcome(result) == crate::specs::part2_associated_codestream_header(
        codestream_header_association_view(selected), associated_header_view(fallback),
    ),
    result == super::associated_header_reference(selected, fallback),
))]
pub(crate) fn associated_header_for_codestream<'a>(
    selected: &'a CodestreamBox<'_>,
    fallback: &'a Jp2Header,
) -> Result<&'a Jp2Header, DecodeError> {
    match &selected.codestream_header {
        Some(association) => match &association.parsed {
            Some(header) => Ok(header),
            None => Err(DecodeError::MalformedInput {
                offset: association.header.offset,
                kind: MalformedKind::MissingRequiredStructure,
            }),
        },
        None => Ok(fallback),
    }
}

impl<'a> CodestreamBox<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::box_header_offset(result) == super::codestream_source_view(self).1,
    ))]
    pub const fn box_header(&self) -> BoxHeader {
        self.header
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == super::codestream_source_view(self).0,
    ))]
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::source_optional_association_view(result) == super::codestream_source_view(self).2,
    ))]
    pub fn codestream_header(&self) -> Option<&CodestreamHeaderAssociation<'a>> {
        self.codestream_header.as_ref()
    }
}

impl CodestreamHeaderAssociation<'_> {
    pub const fn box_header(&self) -> BoxHeader {
        self.header
    }

    pub fn payload(&self) -> &[u8] {
        self.payload
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::associated_header_option(result) == super::source_association_header_view(self).1,
    ))]
    pub fn parsed_header(&self) -> Option<&Jp2Header> {
        self.parsed.as_ref()
    }
}

impl<'a> Jp2File<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::file_type_view(result) == super::jpx_file_decode_view(self).0,
    ))]
    pub fn file_type(&self) -> &FileType {
        &self.file_type
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures super::associated_header_view(result) == super::jpx_file_decode_view(self).2,
            result == super::jpx_file_header_reference(self),
    ))]
    pub fn header(&self) -> &Jp2Header {
        &self.header
    }

    pub fn compositing_layer_count(&self) -> u32 {
        self.compositing_layers.len() as u32
    }

    pub const fn has_composition(&self) -> bool {
        self.composition.is_some()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == super::source_file_layers(self),
    ))]
    pub fn compositing_layers(&self) -> &[CompositingLayer<'a>] {
        &self.compositing_layers
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result {
            Err(error) => crate::specs::part2_layer_config_lookup(super::source_file_layer_configs(self), index) == Err(error),
            Ok(layer) => crate::specs::part2_layer_config_lookup(super::source_file_layer_configs(self), index)
                == Ok(super::source_layer_routing_config(self, layer)),
        },
        match result { Err(_) => true, Ok(layer) => Some(layer) == super::jpx_file_layer_reference(self, index) },
    ))]
    pub fn compositing_layer(&self, index: usize) -> Result<&CompositingLayer<'a>, DecodeError> {
        self.compositing_layers
            .get(index)
            .ok_or(DecodeError::LayerIndexOutOfRange {
                index,
                layers: self.compositing_layers.len(),
            })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::source_file_composition_reference(self),
    ))]
    pub const fn composition(&self) -> Option<&Composition> {
        self.composition.as_ref()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::source_file_metadata(self).0,
    ))]
    pub const fn metadata_boxes(&self) -> u32 {
        self.metadata_boxes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::source_file_metadata(self).1,
    ))]
    pub const fn metadata_depth(&self) -> u32 {
        self.metadata_depth
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::jpx_file_decode_view(self).1.len(),
    ))]
    pub fn codestream_count(&self) -> usize {
        self.codestreams.len()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result {
            Err(error) => crate::specs::part2_jpx_codestream_lookup(
                super::jpx_file_decode_view(self).1, index) == Err(error),
            Ok(stream) => crate::specs::part2_jpx_codestream_lookup(
                super::jpx_file_decode_view(self).1, index) == Ok(super::codestream_source_view(stream)),
        },
        match result {
            Err(_) => true,
            Ok(stream) => Some(stream) == super::jpx_file_codestream_reference(self, index),
        },
    ))]
    pub fn codestream(&self, index: usize) -> Result<&CodestreamBox<'a>, DecodeError> {
        self.codestreams
            .get(index)
            .ok_or(DecodeError::CodestreamIndexOutOfRange {
                index,
                codestreams: self.codestreams.len(),
            })
    }

    pub fn codestreams(&self) -> &[CodestreamBox<'a>] {
        &self.codestreams
    }
}

impl<'a> InspectedJp2<'a> {
    pub fn file(&self) -> &Jp2File<'a> {
        &self.file
    }

    pub fn codestream_count(&self) -> usize {
        self.codestreams.len()
    }

    pub fn codestream(&self, index: usize) -> Result<&CodestreamInfo, DecodeError> {
        self.codestreams
            .get(index)
            .ok_or(DecodeError::CodestreamIndexOutOfRange {
                index,
                codestreams: self.codestreams.len(),
            })
    }

    pub fn codestreams(&self) -> &[CodestreamInfo] {
        &self.codestreams
    }
}

pub fn parse_and_inspect<'a>(
    input: &'a [u8],
    limits: &ResourceLimits,
) -> Result<InspectedJp2<'a>, DecodeError> {
    let file = parse(input, limits)?;
    let codestream_count = file.codestream_count();
    let mut inspected_codestreams = Vec::with_capacity(codestream_count);
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= codestream_count,
            decreases codestream_count - index,
        )
    )]
    while index < codestream_count {
        let codestream_box = file.codestream(index)?;
        let info = codestream::parse(codestream_box.data, limits)?;
        let jph = file.file_type.is_jph_compatible();
        if jph != info.profile.is_part15() {
            return Err(DecodeError::malformed(
                codestream_box.header.offset(),
                MalformedKind::InvalidProfile,
            ));
        }
        let associated_header = match codestream_box.codestream_header() {
            Some(association) => association.parsed.as_ref(),
            None if index == 0 => Some(&file.header),
            None => None,
        };
        if let Some(header) = associated_header {
            validate_container_codestream(header, &info, codestream_box.header.offset())?;
        }
        inspected_codestreams.push(info);
        index = index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    Ok(InspectedJp2 {
        file,
        codestreams: inspected_codestreams,
    })
}

pub fn inspect_jph<'a>(
    input: &'a [u8],
    limits: &ResourceLimits,
) -> Result<InspectedJp2<'a>, DecodeError> {
    let inspected = parse_and_inspect(input, limits)?;
    if !inspected.file.file_type.is_jph_compatible() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidProfile));
    }
    Ok(inspected)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_validate_selected_header(
        header.image, codestream.image_size.width, codestream.image_size.height, codestream.image_size.components,
        codestream.image_size.uniform_bit_depth, codestream.image_size.uniform_signed, offset,
    ),
))]
fn validate_container_codestream(
    header: &Jp2Header,
    codestream: &CodestreamInfo,
    offset: u64,
) -> Result<(), DecodeError> {
    if header.image.width != codestream.image_size.width
        || header.image.height != codestream.image_size.height
        || header.image.components != codestream.image_size.components
    {
        return Err(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::ContainerCodestreamMismatch,
        });
    }

    if let ComponentBitDepth::Uniform { bits, signed } = header.image.bit_depth {
        let matches_depth = match (
            codestream.image_size.uniform_bit_depth,
            codestream.image_size.uniform_signed,
        ) {
            (Some(codestream_bits), Some(codestream_signed)) => {
                codestream_bits == bits && codestream_signed == signed
            }
            _ => false,
        };
        if !matches_depth {
            return Err(DecodeError::MalformedInput {
                offset,
                kind: MalformedKind::ContainerCodestreamMismatch,
            });
        }
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_validate_selected_header(
        header.image, codestream.image_size.width, codestream.image_size.height, codestream.image_size.components,
        codestream.image_size.uniform_bit_depth, codestream.image_size.uniform_signed, offset,
    ),
))]
pub(crate) fn validate_selected_header(
    header: &Jp2Header,
    codestream: &CodestreamInfo,
    offset: u64,
) -> Result<(), DecodeError> {
    validate_container_codestream(header, codestream, offset)
}

pub fn parse<'a>(input: &'a [u8], limits: &ResourceLimits) -> Result<Jp2File<'a>, DecodeError> {
    let mut reader = BoxReader::new(input, limits)?;
    let signature = required_box(&mut reader, 0)?;
    if !signature.header.box_type().equals(BoxType::SIGNATURE)
        || signature.header.total_length() != 12
        || signature.payload.len() != SIGNATURE_MAGIC.len()
        || signature.payload[0] != SIGNATURE_MAGIC[0]
        || signature.payload[1] != SIGNATURE_MAGIC[1]
        || signature.payload[2] != SIGNATURE_MAGIC[2]
        || signature.payload[3] != SIGNATURE_MAGIC[3]
    {
        return Err(DecodeError::malformed(
            signature.header.offset(),
            MalformedKind::InvalidSignature,
        ));
    }

    let file_type_box = required_box(&mut reader, 1)?;
    if !file_type_box.header.box_type().equals(BoxType::FILE_TYPE) {
        return Err(DecodeError::malformed(
            file_type_box.header.offset(),
            MalformedKind::InvalidBoxOrder,
        ));
    }
    let file_type = parse_file_type(file_type_box, limits)?;
    validate_file_type_profile(&file_type, file_type_box.header.offset())?;
    if !file_type.is_compatible_with(BoxType::JP2_BRAND)
        && !file_type.is_jpx_compatible()
        && !file_type.is_compatible_with(BoxType::JPH_BRAND)
    {
        return Err(DecodeError::UnsupportedProfile {
            feature: "unrecognized JPEG 2000 file brand",
        });
    }

    let mut parsed_header = None;
    let mut codestream_boxes = Vec::new();
    let mut codestream_headers = Vec::new();
    let mut compositing_layers = Vec::new();
    let mut composition = None;
    let mut metadata_boxes = 0_u32;
    let mut metadata_depth = 0_u32;
    let mut box_count = 2_u64;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(decreases input.len() as int - reader.position as int,)
    )]
    loop {
        let previous_position = reader.position;
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if reader.position <= previous_position || reader.position > input.len() {
            return Err(DecodeError::malformed(
                previous_position as u64,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let box_ref = next?;
        box_count = box_count
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let box_type = box_ref.header.box_type();
        if box_type.equals(BoxType::JP2_HEADER) {
            if parsed_header.is_some()
                || !codestream_boxes.is_empty()
                || !codestream_headers.is_empty()
                || !compositing_layers.is_empty()
                || composition.is_some()
            {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            parsed_header = Some(parse_jp2_header(
                box_ref.payload,
                limits,
                box_ref.header.payload_offset()?,
            )?);
        } else if box_type.equals(BoxType::CODESTREAM_HEADER) {
            if !file_type.is_jpx_compatible() {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidFileType,
                ));
            }
            if parsed_header.is_none() || !codestream_boxes.is_empty() {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let actual = u64::try_from(codestream_headers.len())
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| {
                    DecodeError::malformed(
                        box_ref.header.offset(),
                        MalformedKind::ArithmeticOverflow,
                    )
                })?;
            if actual > u64::from(limits.maximum_codestreams()) {
                return Err(DecodeError::limit(
                    Resource::Codestreams,
                    u64::from(limits.maximum_codestreams()),
                    actual,
                ));
            }
            let payload_offset = box_ref.header.payload_offset()?;
            let parsed = match parse_codestream_header(
                box_ref.payload,
                parsed_header.as_ref(),
                limits,
                payload_offset,
            ) {
                Ok(header) => Some(header),
                Err(error) => return Err(error),
            };
            codestream_headers.push(CodestreamHeaderAssociation {
                header: box_ref.header,
                payload: box_ref.payload,
                parsed,
            });
        } else if box_type.equals(BoxType::COMPOSITING_LAYER_HEADER) {
            if !file_type.is_jpx_compatible() {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidFileType,
                ));
            }
            if parsed_header.is_none() || !codestream_boxes.is_empty() || composition.is_some() {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let actual = compositing_layers.len().checked_add(1).ok_or_else(|| {
                DecodeError::malformed(box_ref.header.offset(), MalformedKind::ArithmeticOverflow)
            })?;
            if actual as u64 > u64::from(limits.maximum_layers()) {
                return Err(DecodeError::limit(
                    Resource::Layers,
                    u64::from(limits.maximum_layers()),
                    actual as u64,
                ));
            }
            compositing_layers.push(parse_compositing_layer(box_ref, limits)?);
        } else if box_type.equals(BoxType::COMPOSITION) {
            if !file_type.is_jpx_compatible() {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidFileType,
                ));
            }
            if parsed_header.is_none()
                || !codestream_boxes.is_empty()
                || composition.is_some()
                || compositing_layers.is_empty()
            {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            composition = Some(parse_composition(box_ref, limits)?);
        } else if box_type.equals(BoxType::CONTIGUOUS_CODESTREAM) {
            if parsed_header.is_none() {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            let actual = u64::try_from(codestream_boxes.len())
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| {
                    DecodeError::malformed(
                        box_ref.header.offset(),
                        MalformedKind::ArithmeticOverflow,
                    )
                })?;
            if actual > u64::from(limits.maximum_codestreams()) {
                return Err(DecodeError::limit(
                    Resource::Codestreams,
                    u64::from(limits.maximum_codestreams()),
                    actual,
                ));
            }
            if actual > 1 && !file_type.is_jpx_compatible() {
                return Err(DecodeError::malformed(
                    box_ref.header.offset(),
                    MalformedKind::InvalidBoxContents,
                ));
            }
            codestream_boxes.push(CodestreamBox {
                header: box_ref.header,
                data: box_ref.payload,
                codestream_header: None,
            });
        } else {
            let (count, depth) = inspect_metadata_box(box_ref, limits, 1, u32::MAX - 1)?;
            metadata_boxes = metadata_boxes
                .checked_add(count)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            metadata_depth = metadata_depth.max(depth);
        }
    }

    let header = parsed_header
        .ok_or_else(|| DecodeError::malformed(0, MalformedKind::MissingRequiredStructure))?;
    if codestream_boxes.is_empty() {
        return Err(DecodeError::malformed(
            0,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    if codestream_headers.len() > codestream_boxes.len() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
    }
    let mut header_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant header_index <= codestream_headers.len(),
            decreases codestream_headers.len() - header_index,
        )
    )]
    while header_index < codestream_headers.len() {
        let association = codestream_headers
            .get(header_index)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?
            .clone();
        let codestream_box = codestream_boxes
            .get_mut(header_index)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidBoxContents))?;
        codestream_box.codestream_header = Some(association);
        header_index = header_index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    validate_layer_references(&compositing_layers, codestream_boxes.len())?;
    Ok(Jp2File {
        file_type,
        header,
        codestreams: codestream_boxes,
        compositing_layers,
        composition,
        metadata_boxes,
        metadata_depth,
        box_count,
    })
}

fn parse_file_type(box_ref: BoxRef<'_>, limits: &ResourceLimits) -> Result<FileType, DecodeError> {
    let payload_offset = box_ref.header.payload_offset()?;
    if box_ref.payload.len() < 8 || !box_ref.payload.len().is_multiple_of(4) {
        return Err(DecodeError::malformed(
            payload_offset,
            MalformedKind::InvalidBoxLength,
        ));
    }

    let compatible_brand_count = box_ref
        .payload
        .len()
        .checked_sub(8)
        .and_then(|bytes| bytes.checked_div(4))
        .ok_or_else(|| DecodeError::malformed(payload_offset, MalformedKind::ArithmeticOverflow))?;
    let compatible_brand_count_u64 = u64::try_from(compatible_brand_count)
        .map_err(|_| DecodeError::malformed(payload_offset, MalformedKind::ArithmeticOverflow))?;
    if compatible_brand_count_u64 > u64::from(limits.maximum_compatible_brands()) {
        return Err(DecodeError::limit(
            Resource::CompatibleBrands,
            u64::from(limits.maximum_compatible_brands()),
            compatible_brand_count_u64,
        ));
    }
    let brand = BoxType::new([
        box_ref.payload[0],
        box_ref.payload[1],
        box_ref.payload[2],
        box_ref.payload[3],
    ]);
    let mut compatible_brands: Vec<BoxType> = Vec::new();
    let mut position = 8_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= box_ref.payload.len(),
            decreases box_ref.payload.len() - position,
        )
    )]
    while position < box_ref.payload.len() {
        let compatible = read_box_type_at(box_ref.payload, position, payload_offset)?;
        let mut prior = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant prior <= compatible_brands.len(),
                decreases compatible_brands.len() - prior,
            )
        )]
        while prior < compatible_brands.len() {
            let previous = compatible_brands.get(prior).ok_or_else(|| {
                DecodeError::malformed(box_ref.header.offset(), MalformedKind::ArithmeticOverflow)
            })?;
            if previous.equals(compatible) {
                return Err(DecodeError::malformed(
                    payload_offset,
                    MalformedKind::InvalidBoxContents,
                ));
            }
            prior = prior.checked_add(1).ok_or_else(|| {
                DecodeError::malformed(box_ref.header.offset(), MalformedKind::ArithmeticOverflow)
            })?;
        }
        compatible_brands.push(compatible);
        position = position.checked_add(4).ok_or_else(|| {
            DecodeError::malformed(box_ref.header.offset(), MalformedKind::ArithmeticOverflow)
        })?;
        if position > box_ref.payload.len() {
            return Err(DecodeError::malformed(
                payload_offset,
                MalformedKind::InvalidBoxLength,
            ));
        }
    }
    Ok(FileType {
        brand,
        minor_version: read_u32([
            box_ref.payload[4],
            box_ref.payload[5],
            box_ref.payload[6],
            box_ref.payload[7],
        ]),
        compatible_brands,
    })
}

fn validate_file_type_profile(file_type: &FileType, offset: u64) -> Result<(), DecodeError> {
    if file_type.brand.equals(BoxType::JP2_BRAND) && file_type.is_jpx_compatible() {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidFileType,
        ));
    }
    if !file_type.is_jph_compatible() {
        return Ok(());
    }
    if !crate::refinement::part15_jph_branding(
        file_type.brand.equals(BoxType::JPH_BRAND),
        file_type.minor_version,
        file_type.compatible_brands.len(),
        file_type.compatible_brands.len() == 1
            && file_type.compatible_brands[0].equals(BoxType::JPH_BRAND),
    ) {
        return Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidProfile,
        ));
    }
    Ok(())
}
