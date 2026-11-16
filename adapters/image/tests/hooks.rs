use std::io::Cursor;

use image::{ColorType, GenericImageView, ImageError, ImageReader, Limits};
use jpeg2000_image::{DecoderOptions, RawColorSpace, register_decoding_hooks};

#[test]
fn public_image_paths_dispatch_and_propagate_failures() {
    let options = DecoderOptions {
        raw_color_space: Some(RawColorSpace::Srgb),
        ..Default::default()
    };
    register_decoding_hooks(options).unwrap();
    let fixture = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/rgb8.jp2");
    let image = ImageReader::open(fixture).unwrap().decode().unwrap();
    assert_eq!(image.color(), ColorType::Rgb16);
    assert_eq!(image.dimensions(), (9, 7));
    assert_eq!(
        image.as_rgb16().unwrap().get_pixel(0, 0).0,
        [0, 71 * 257, 142 * 257]
    );
    for bytes in [
        include_bytes!("fixtures/rgb8.jp2").as_slice(),
        include_bytes!("fixtures/raw-rgb8.j2k").as_slice(),
    ] {
        let image = image::load_from_memory(bytes).unwrap();
        assert_eq!(image.color(), ColorType::Rgb16);
        assert_eq!(image.dimensions(), (9, 7));
        let mut reader = ImageReader::new(Cursor::new(bytes))
            .with_guessed_format()
            .unwrap();
        let mut limits = Limits::no_limits();
        limits.max_image_width = Some(8);
        reader.limits(limits);
        assert!(matches!(reader.decode(), Err(ImageError::Limits(_))));
    }
    let mut reader = ImageReader::open(fixture).unwrap();
    let mut limits = Limits::no_limits();
    limits.max_alloc = Some(9 * 7 * 3 * 2);
    reader.limits(limits);
    assert!(matches!(reader.decode(), Err(ImageError::Limits(_))));
    assert!(image::load_from_memory(&include_bytes!("fixtures/rgb8.jp2")[..40]).is_err());
    let error = register_decoding_hooks(options).unwrap_err();
    assert_eq!(error.extension, "jp2");
}
