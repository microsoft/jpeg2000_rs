#![forbid(unsafe_code)]
#![doc = include_str!("../README.md")]

use std::io::Read;

use image::error::{
    DecodingError, ImageFormatHint, LimitError, LimitErrorKind, UnsupportedError,
    UnsupportedErrorKind,
};
use image::{ColorType, ImageDecoder, ImageError, ImageResult, LimitSupport, Limits};
use jpeg2000_decoder::jp2::{
    self, BoxType, ColorMethod, ColorSpecification, ENUMERATED_GRAYSCALE, ENUMERATED_SRGB,
    ENUMERATED_SYCC,
};
use jpeg2000_decoder::{
    ChannelAssociation, ChannelType, ConvertedChannelType, ConvertedColorSpace, DecodeError,
    DecodeOptions, Resource, codestream,
};

mod hooks;
pub use hooks::{HookRegistrationError, register_decoding_hooks};
pub use jpeg2000_decoder::ResourceLimits;

/// Interpretation of decoded components in an untagged raw codestream.
///
/// These refer to components *after* the decoder's inverse component transforms.
#[derive(Clone, Copy, Debug)]
pub enum RawColorSpace {
    /// Exactly one grayscale component.
    Grayscale,
    /// Exactly three sRGB components.
    Srgb,
}

/// Options applied before input buffering and header inspection.
#[derive(Clone, Copy, Debug, Default)]
pub struct DecoderOptions {
    /// Codec resource caps. These remain in force even with `ImageReader::no_limits`.
    pub limits: ResourceLimits,
    /// Raw codestreams are rejected unless their color interpretation is explicit.
    pub raw_color_space: Option<RawColorSpace>,
}

/// An owned, deferred JPEG 2000 decoder implementing [`image::ImageDecoder`].
///
/// Construction buffers bounded compressed input and inspects headers, but does
/// not decode pixels. Output is always normalized, native-endian U16.
pub struct Jpeg2000Decoder {
    input: Vec<u8>,
    options: DecoderOptions,
    metadata: Metadata,
    image_limits: Limits,
}

struct Metadata {
    width: u32,
    height: u32,
    color: ColorType,
    raw: bool,
}

impl Jpeg2000Decoder {
    /// Construct a decoder using hardened codec defaults. Untagged raw input is rejected.
    pub fn new(reader: impl Read) -> ImageResult<Self> {
        Self::with_options(reader, DecoderOptions::default())
    }

    /// Construct a decoder with input and codec caps set before reading.
    ///
    /// `image` hooks receive their caller's limits only after construction.
    /// Configure `options.limits` here to constrain input buffering and inspection.
    pub fn with_options(mut reader: impl Read, options: DecoderOptions) -> ImageResult<Self> {
        let maximum = options.limits.maximum_input_bytes();
        let mut input = Vec::new();
        reader.by_ref().take(maximum).read_to_end(&mut input)?;
        if input.len() as u64 == maximum {
            let mut probe = [0];
            loop {
                match reader.read(&mut probe) {
                    Ok(0) => break,
                    Ok(_) => {
                        return Err(codec_error(DecodeError::LimitExceeded {
                            resource: Resource::InputBytes,
                            limit: maximum,
                            actual: maximum + 1,
                        }));
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(error.into()),
                }
            }
        }
        let metadata = inspect(&input, options)?;
        let decoder = Self {
            input,
            options,
            metadata,
            image_limits: Limits::no_limits(),
        };
        usize::try_from(decoder.total_bytes()).map_err(|_| memory_limit())?;
        Ok(decoder)
    }

    fn codec_options(&self) -> ImageResult<DecodeOptions> {
        self.image_limits
            .check_dimensions(self.metadata.width, self.metadata.height)?;
        let mut remaining = self.image_limits.clone();
        // ImageReader has already reserved the caller-owned output.
        remaining.reserve_usize(self.input.capacity())?;
        let mut limits = self.options.limits;
        if let Some(bytes) = remaining.max_alloc {
            limits = limits
                .with_maximum_decoded_bytes(bytes.min(limits.maximum_decoded_bytes()))
                .map_err(codec_error)?;
        }
        Ok(DecodeOptions::new(limits))
    }
}

impl ImageDecoder for Jpeg2000Decoder {
    fn dimensions(&self) -> (u32, u32) {
        (self.metadata.width, self.metadata.height)
    }

    fn color_type(&self) -> ColorType {
        self.metadata.color
    }

    fn set_limits(&mut self, limits: Limits) -> ImageResult<()> {
        limits.check_support(&LimitSupport::default())?;
        limits.check_dimensions(self.metadata.width, self.metadata.height)?;
        let mut remaining = limits.clone();
        remaining.reserve_usize(self.input.capacity())?;
        self.image_limits = limits;
        Ok(())
    }

    fn read_image(self, buf: &mut [u8]) -> ImageResult<()> {
        assert_eq!(buf.len() as u64, self.total_bytes());
        let options = self.codec_options()?;
        let image = if self.metadata.raw {
            let raw =
                jpeg2000_decoder::decode_codestream(&self.input, &options).map_err(codec_error)?;
            let color = raw_color(self.options.raw_color_space)?;
            jpeg2000_decoder::convert_jp2_color(&raw, &color, options.limits())
                .map_err(codec_error)?
        } else {
            jpeg2000_decoder::decode_jp2_color(&self.input, &options).map_err(codec_error)?
        };
        let expected: &[ConvertedChannelType] = match self.metadata.color {
            ColorType::L16 => &[ConvertedChannelType::Gray],
            ColorType::La16 => &[ConvertedChannelType::Gray, STRAIGHT_ALPHA],
            ColorType::Rgb16 => &[
                ConvertedChannelType::Red,
                ConvertedChannelType::Green,
                ConvertedChannelType::Blue,
            ],
            ColorType::Rgba16 => &[
                ConvertedChannelType::Red,
                ConvertedChannelType::Green,
                ConvertedChannelType::Blue,
                STRAIGHT_ALPHA,
            ],
            _ => return Err(invalid_output()),
        };
        let pixels = buf.len() / (expected.len() * 2);
        if image.width() != self.metadata.width
            || image.height() != self.metadata.height
            || image.precision() != 16
            || image.channels().len() != expected.len()
            || image
                .channels()
                .iter()
                .zip(expected)
                .any(|(channel, kind)| {
                    channel.channel_type() != *kind || channel.samples().len() != pixels
                })
        {
            return Err(invalid_output());
        }
        for (index, pixel) in buf.chunks_exact_mut(expected.len() * 2).enumerate() {
            for (sample, channel) in pixel.chunks_exact_mut(2).zip(image.channels()) {
                sample.copy_from_slice(&channel.samples()[index].to_ne_bytes());
            }
        }
        Ok(())
    }

    fn read_image_boxed(self: Box<Self>, buf: &mut [u8]) -> ImageResult<()> {
        (*self).read_image(buf)
    }
}

const STRAIGHT_ALPHA: ConvertedChannelType = ConvertedChannelType::Alpha {
    premultiplied: false,
    association: ChannelAssociation::WholeImage,
};

fn inspect(input: &[u8], options: DecoderOptions) -> ImageResult<Metadata> {
    if input.starts_with(&[0xff, 0x4f]) {
        let info = codestream::parse(input, &options.limits).map_err(codec_error)?;
        let color = raw_color(options.raw_color_space)?;
        let (space, components) = match color.method() {
            ColorMethod::Enumerated {
                color_space: ENUMERATED_GRAYSCALE,
            } => (ConvertedColorSpace::Grayscale, 1),
            _ => (ConvertedColorSpace::Srgb, 3),
        };
        if info.image_size.components != components {
            return Err(unsupported(
                "raw component count does not match the requested color space",
            ));
        }
        return Ok(Metadata {
            width: info.image_size.width,
            height: info.image_size.height,
            color: output_color(space, false),
            raw: true,
        });
    }
    let inspected = jp2::parse_and_inspect(input, &options.limits).map_err(codec_error)?;
    let file = inspected.file();
    if !file.file_type().is_compatible_with(BoxType::JP2_BRAND)
        || file.file_type().is_jpx_compatible()
        || file.file_type().is_jph_compatible()
        || file.codestream_count() != 1
    {
        return Err(unsupported(
            "only single-codestream JP2 containers are supported",
        ));
    }
    let header = file.header();
    let space = match header.color.method() {
        ColorMethod::Enumerated {
            color_space: ENUMERATED_GRAYSCALE,
        } => ConvertedColorSpace::Grayscale,
        ColorMethod::Enumerated {
            color_space: ENUMERATED_SRGB | ENUMERATED_SYCC,
        } => ConvertedColorSpace::Srgb,
        _ => {
            return Err(unsupported(
                "only enumerated grayscale, sRGB and sYCC color are supported",
            ));
        }
    };
    let mut alpha = false;
    for channel in &header.channel_definition_records {
        match channel.definition.channel_type() {
            ChannelType::Opacity => {
                if alpha || channel.definition.association() != ChannelAssociation::WholeImage {
                    return Err(unsupported(
                        "only one whole-image alpha channel is supported",
                    ));
                }
                alpha = true;
            }
            ChannelType::PremultipliedOpacity => {
                return Err(unsupported("premultiplied alpha is not supported"));
            }
            _ => {}
        }
    }
    Ok(Metadata {
        width: header.image.width,
        height: header.image.height,
        color: output_color(space, alpha),
        raw: false,
    })
}

fn raw_color(color: Option<RawColorSpace>) -> ImageResult<ColorSpecification> {
    let value = match color {
        Some(RawColorSpace::Grayscale) => ENUMERATED_GRAYSCALE,
        Some(RawColorSpace::Srgb) => ENUMERATED_SRGB,
        None => {
            return Err(unsupported(
                "untagged raw codestreams require an explicit color space",
            ));
        }
    };
    Ok(ColorSpecification::enumerated(value))
}

fn output_color(space: ConvertedColorSpace, alpha: bool) -> ColorType {
    match (space, alpha) {
        (ConvertedColorSpace::Grayscale, false) => ColorType::L16,
        (ConvertedColorSpace::Grayscale, true) => ColorType::La16,
        (ConvertedColorSpace::Srgb, false) => ColorType::Rgb16,
        (ConvertedColorSpace::Srgb, true) => ColorType::Rgba16,
    }
}

fn format_hint() -> ImageFormatHint {
    ImageFormatHint::Name("JPEG 2000".into())
}

fn unsupported(message: impl Into<String>) -> ImageError {
    ImageError::Unsupported(UnsupportedError::from_format_and_kind(
        format_hint(),
        UnsupportedErrorKind::GenericFeature(message.into()),
    ))
}

fn memory_limit() -> ImageError {
    ImageError::Limits(LimitError::from_kind(LimitErrorKind::InsufficientMemory))
}

fn invalid_output() -> ImageError {
    ImageError::Decoding(DecodingError::new(
        format_hint(),
        "unexpected converted output layout",
    ))
}

fn codec_error(error: DecodeError) -> ImageError {
    match error {
        DecodeError::LimitExceeded {
            resource: Resource::Width | Resource::Height | Resource::Pixels,
            ..
        } => ImageError::Limits(LimitError::from_kind(LimitErrorKind::DimensionError)),
        DecodeError::LimitExceeded {
            resource: Resource::InputBytes | Resource::MetadataBytes | Resource::DecodedBytes,
            ..
        } => memory_limit(),
        DecodeError::UnsupportedProfile { .. }
        | DecodeError::UnsupportedFeature { .. }
        | DecodeError::UnsupportedComposition { .. }
        | DecodeError::UnsupportedLayer { .. }
        | DecodeError::UnsupportedTransform { .. }
        | DecodeError::UnsupportedColorConversion { .. } => unsupported(error.to_string()),
        _ => ImageError::Decoding(DecodingError::new(format_hint(), error)),
    }
}
