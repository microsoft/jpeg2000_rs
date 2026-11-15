use std::io::{self, Cursor, Read};

use image::{ColorType, DynamicImage, ImageDecoder, ImageError, Limits};
use jpeg2000_image::{DecoderOptions, Jpeg2000Decoder, RawColorSpace, ResourceLimits};

const RGB: &[u8] = include_bytes!("fixtures/rgb8.jp2");

fn words(bytes: &[u8]) -> Vec<u16> {
    bytes
        .chunks_exact(2)
        .map(|p| u16::from_le_bytes([p[0], p[1]]))
        .collect()
}

#[test]
fn lossless_jp2_pixels_and_native_endian_unaligned_output() {
    let cases: &[(&[u8], &[u8], ColorType)] = &[
        (
            include_bytes!("fixtures/gray8.jp2"),
            include_bytes!("fixtures/gray8.u16le"),
            ColorType::L16,
        ),
        (RGB, include_bytes!("fixtures/rgb8.u16le"), ColorType::Rgb16),
        (
            include_bytes!("fixtures/rgba8.jp2"),
            include_bytes!("fixtures/rgba8.u16le"),
            ColorType::Rgba16,
        ),
        (
            include_bytes!("fixtures/gray-alpha8.jp2"),
            include_bytes!("fixtures/gray-alpha8.u16le"),
            ColorType::La16,
        ),
        (
            include_bytes!("fixtures/gray16.jp2"),
            include_bytes!("fixtures/gray16.u16le"),
            ColorType::L16,
        ),
        (
            include_bytes!("fixtures/rgb-origin8.jp2"),
            include_bytes!("fixtures/rgb-origin8.u16le"),
            ColorType::Rgb16,
        ),
        (
            include_bytes!("fixtures/rgb-tiled8.jp2"),
            include_bytes!("fixtures/rgb-tiled8.u16le"),
            ColorType::Rgb16,
        ),
        (
            include_bytes!("fixtures/palette8.jp2"),
            include_bytes!("fixtures/palette8.u16le"),
            ColorType::Rgb16,
        ),
        (
            include_bytes!("fixtures/reordered8.jp2"),
            include_bytes!("fixtures/reordered8.u16le"),
            ColorType::Rgb16,
        ),
        (
            include_bytes!("fixtures/sycc8.jp2"),
            include_bytes!("fixtures/sycc8.u16le"),
            ColorType::Rgb16,
        ),
    ];
    for &(encoded, expected, color) in cases {
        let decoder = Jpeg2000Decoder::new(encoded).unwrap();
        assert_eq!(decoder.dimensions(), (9, 7));
        assert_eq!(decoder.color_type(), color);
        let image = DynamicImage::from_decoder(decoder).unwrap();
        let actual: Vec<u16> = image
            .as_bytes()
            .chunks_exact(2)
            .map(|p| u16::from_ne_bytes([p[0], p[1]]))
            .collect();
        assert_eq!(actual, words(expected));

        let decoder = Jpeg2000Decoder::new(encoded).unwrap();
        let mut output = vec![0x5a; decoder.total_bytes() as usize + 2];
        decoder
            .read_image(&mut output[1..expected.len() + 1])
            .unwrap();
        assert_eq!(output[0], 0x5a);
        assert_eq!(output[expected.len() + 1], 0x5a);
        let actual: Vec<u16> = output[1..expected.len() + 1]
            .chunks_exact(2)
            .map(|p| u16::from_ne_bytes([p[0], p[1]]))
            .collect();
        assert_eq!(actual, words(expected));
    }
}

#[test]
fn raw_codestreams_require_matching_explicit_color() {
    for (input, expected, color) in [
        (
            include_bytes!("fixtures/raw-rgb8.j2k").as_slice(),
            include_bytes!("fixtures/raw-rgb8.u16le").as_slice(),
            RawColorSpace::Srgb,
        ),
        (
            include_bytes!("fixtures/raw-gray8.j2k").as_slice(),
            include_bytes!("fixtures/raw-gray8.u16le").as_slice(),
            RawColorSpace::Grayscale,
        ),
    ] {
        assert!(matches!(
            Jpeg2000Decoder::new(input),
            Err(ImageError::Unsupported(_))
        ));
        let options = DecoderOptions {
            raw_color_space: Some(color),
            ..Default::default()
        };
        let image =
            DynamicImage::from_decoder(Jpeg2000Decoder::with_options(input, options).unwrap())
                .unwrap();
        let actual: Vec<u16> = image
            .as_bytes()
            .chunks_exact(2)
            .map(|p| u16::from_ne_bytes([p[0], p[1]]))
            .collect();
        assert_eq!(actual, words(expected));
    }
    let options = DecoderOptions {
        raw_color_space: Some(RawColorSpace::Grayscale),
        ..Default::default()
    };
    assert!(matches!(
        Jpeg2000Decoder::with_options(include_bytes!("fixtures/raw-rgb8.j2k").as_slice(), options),
        Err(ImageError::Unsupported(_))
    ));
}

struct InfiniteInput {
    read: usize,
}

impl Read for InfiniteInput {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        bytes.fill(0);
        self.read += bytes.len();
        Ok(bytes.len())
    }
}

#[test]
fn input_is_bounded_before_header_parsing() {
    let mut reader = InfiniteInput { read: 0 };
    let options = DecoderOptions {
        limits: ResourceLimits::default()
            .with_maximum_input_bytes(31)
            .unwrap(),
        ..Default::default()
    };
    assert!(matches!(
        Jpeg2000Decoder::with_options(&mut reader, options),
        Err(ImageError::Limits(_))
    ));
    assert_eq!(reader.read, 32);
    let options = DecoderOptions {
        limits: ResourceLimits::default()
            .with_maximum_input_bytes(RGB.len() as u64)
            .unwrap(),
        ..Default::default()
    };
    assert!(Jpeg2000Decoder::with_options(RGB, options).is_ok());
}

#[test]
fn image_dimensions_and_working_memory_limits_propagate() {
    let mut decoder = Jpeg2000Decoder::new(RGB).unwrap();
    let mut limits = Limits::no_limits();
    limits.max_image_width = Some(8);
    assert!(matches!(
        decoder.set_limits(limits),
        Err(ImageError::Limits(_))
    ));
    let mut limits = Limits::no_limits();
    limits.max_image_height = Some(6);
    assert!(matches!(
        decoder.set_limits(limits),
        Err(ImageError::Limits(_))
    ));

    let mut limits = Limits::no_limits();
    limits.max_alloc = Some(0);
    assert!(matches!(
        decoder.set_limits(limits),
        Err(ImageError::Limits(_))
    ));

    let options = DecoderOptions {
        limits: ResourceLimits::default()
            .with_maximum_decoded_bytes(0)
            .unwrap(),
        ..Default::default()
    };
    let result = Jpeg2000Decoder::with_options(RGB, options).and_then(DynamicImage::from_decoder);
    assert!(matches!(result, Err(ImageError::Limits(_))));
}

struct FailedReader;
impl Read for FailedReader {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "fixture read denied",
        ))
    }
}

#[test]
fn zero_input_budget_only_probes_one_byte() {
    let mut reader = InfiniteInput { read: 0 };
    let options = DecoderOptions {
        limits: ResourceLimits::default()
            .with_maximum_input_bytes(0)
            .unwrap(),
        ..Default::default()
    };
    assert!(matches!(
        Jpeg2000Decoder::with_options(&mut reader, options),
        Err(ImageError::Limits(_))
    ));
    assert_eq!(reader.read, 1);
}

#[test]
fn malformed_inputs_and_io_failures_are_not_successes() {
    for input in [&[][..], b"not a JP2", &RGB[..RGB.len() - 3]] {
        assert!(Jpeg2000Decoder::new(input).is_err());
    }
    let Err(ImageError::IoError(error)) = Jpeg2000Decoder::new(FailedReader) else {
        panic!("reader failure must remain an I/O error");
    };
    assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
}

#[test]
fn codec_work_limit_diagnostic_is_preserved() {
    let options = DecoderOptions {
        limits: ResourceLimits::default()
            .with_maximum_work_units(0)
            .unwrap(),
        ..Default::default()
    };
    let Err(error) = Jpeg2000Decoder::with_options(RGB, options) else {
        panic!("zero work budget must fail");
    };
    assert!(error.to_string().contains("WorkUnits"), "{error}");
}

#[test]
fn unsupported_color_and_premultiplied_alpha_are_explicit_errors() {
    let mut cmyk = RGB.to_vec();
    let colr = cmyk.windows(4).position(|w| w == b"colr").unwrap();
    cmyk[colr + 10] = 12;
    assert!(matches!(
        Jpeg2000Decoder::new(cmyk.as_slice()),
        Err(ImageError::Unsupported(_))
    ));

    let mut alpha = include_bytes!("fixtures/rgba8.jp2").to_vec();
    let cdef = alpha.windows(4).position(|w| w == b"cdef").unwrap();
    let count = u16::from_be_bytes([alpha[cdef + 4], alpha[cdef + 5]]) as usize;
    let mut changed = false;
    for entry in alpha[cdef + 6..cdef + 6 + count * 6].chunks_exact_mut(6) {
        if entry[2..4] == [0, 1] {
            entry[3] = 2;
            changed = true;
        }
    }
    assert!(changed);
    assert!(matches!(
        Jpeg2000Decoder::new(Cursor::new(alpha)),
        Err(ImageError::Unsupported(_))
    ));
}
