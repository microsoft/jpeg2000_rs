#![forbid(unsafe_code)]

use codec::{decode_codestream_selected, DecodeOptions, DecodeSelection, ImageRegion};
use std::{env, fs, hint::black_box, time::Instant};

#[global_allocator]
static ALLOCATOR: std::alloc::System = std::alloc::System;

fn expected(pixels: &[u8], roi: bool) -> String {
    let (x, y, width, height, samples) = if roi {
        (31, 31, 1, 1, vec![u64::from(pixels[1023])])
    } else {
        (
            0,
            0,
            32,
            32,
            pixels.iter().map(|&value| u64::from(value)).collect(),
        )
    };
    format!(
        "TypedImage {{ width: {width}, height: {height}, x_origin: {x}, y_origin: {y}, components: [TypedComponent {{ width: {width}, height: {height}, info: ComponentInfo {{ precision: 8, signed: false, x_subsampling: 1, y_subsampling: 1, x_registration: 0, y_registration: 0 }}, samples: Unsigned({samples:?}), channel_definitions: [] }}] }}"
    )
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [operation, mode, input, pgm] = args.as_slice() else {
        return Err("expected <preflight|bench-fixed> <full|roi> INPUT PGM".into());
    };
    if !matches!(operation.as_str(), "preflight" | "bench-fixed") {
        return Err("expected preflight or bench-fixed".into());
    }
    let roi = match mode.as_str() {
        "full" => false,
        "roi" => true,
        _ => return Err("expected full or roi".into()),
    };
    let data = fs::read(input)?;
    let pgm = fs::read(pgm)?;
    let prefix = b"P5\n32 32\n255\n";
    if !pgm.starts_with(prefix) || pgm.len() != prefix.len() + 1024 {
        return Err("expected the pinned 32x32 P5 source".into());
    }
    let pixels = &pgm[prefix.len()..];
    let literal = expected(pixels, roi);
    let mut wrong = pixels.to_vec();
    wrong[if roi { 1023 } else { 0 }] ^= 1;
    assert_ne!(expected(&wrong, roi), literal);
    assert_ne!(
        literal.replace("x_subsampling: 1", "x_subsampling: 2"),
        literal
    );
    assert_ne!(
        literal.replace("channel_definitions: []", "channel_definitions: [wrong]"),
        literal
    );
    let options = DecodeOptions::default();
    let mut selection = DecodeSelection::full_image().with_discard_levels(0);
    if roi {
        selection = selection.with_region(ImageRegion::new(31, 31, 1, 1));
    }
    let decode = || decode_codestream_selected(black_box(&data), &options, &selection);
    let image = decode()?;
    let actual = format!("{image:?}");
    if actual != literal {
        return Err("complete seeded sample/geometry/component/CDEF mismatch".into());
    }
    drop(image);
    if operation == "preflight" {
        println!("{actual}");
        return Ok(());
    }
    drop(black_box(decode()?));
    let start = Instant::now();
    drop(black_box(decode()?));
    let calibration = start.elapsed().as_nanos();
    let mut samples = [0; 3];
    for sample in &mut samples {
        let start = Instant::now();
        drop(black_box(decode()?));
        *sample = start.elapsed().as_nanos();
    }
    println!("CONFIG\t3\t1\t{calibration}");
    for elapsed in samples {
        println!("SAMPLE\t{elapsed}");
    }
    println!("LIFECYCLE\t6\t3");
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("scaling probe failed: {error}");
        std::process::exit(1);
    }
}
