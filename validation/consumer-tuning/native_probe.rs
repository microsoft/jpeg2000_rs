#![forbid(unsafe_code)]

use codec::image::DecodedImage;
use codec::{DecodeOptions, decode_codestream_reconstructed};
use std::{
    alloc::System,
    env,
    error::Error,
    fs,
    hint::black_box,
    io::{self, Write},
    time::Instant,
};

#[global_allocator]
static ALLOCATOR: System = System;

fn native_words(
    image: &DecodedImage,
    mut word: impl FnMut(u64) -> io::Result<()>,
) -> io::Result<()> {
    for value in [
        1, // reconstructed i64 sample planes
        u64::from(image.width()),
        u64::from(image.height()),
        u64::from(image.x_origin()),
        u64::from(image.y_origin()),
        image.components().len() as u64,
    ] {
        word(value)?;
    }
    for component in image.components() {
        let info = component.info();
        for value in [
            u64::from(component.width()),
            u64::from(component.height()),
            u64::from(info.precision),
            u64::from(info.signed),
            u64::from(info.x_subsampling),
            u64::from(info.y_subsampling),
            u64::from(info.x_registration),
            u64::from(info.y_registration),
            u64::from(component.fraction_bits()),
            component.samples().len() as u64,
        ] {
            word(value)?;
        }
        for &value in component.samples() {
            word(value as u64)?;
        }
    }
    Ok(())
}

fn run() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [operation, path] = args.as_slice() else {
        return Err("usage: native-probe <dump|bench> INPUT".into());
    };
    if !matches!(operation.as_str(), "dump" | "bench") {
        return Err("invalid operation".into());
    }
    let data = fs::read(path)?;
    let options = DecodeOptions::default();
    let decode = || decode_codestream_reconstructed(black_box(&data), &options);
    let first = decode()?;
    let mut out = io::BufWriter::new(io::stdout().lock());
    if operation == "dump" {
        native_words(&first, |v| out.write_all(&v.to_le_bytes()))?;
    } else {
        let mut hash = 14_695_981_039_346_656_037_u64;
        native_words(&first, |v| {
            // Cheap stability check on the first warm-up, not the preflight parity oracle.
            hash = (hash ^ v).wrapping_mul(1_099_511_628_211);
            Ok(())
        })?;
        drop(first);
        drop(black_box(decode()?));
        let mut times = [0; 3];
        for time in &mut times {
            let start = Instant::now();
            drop(black_box(decode()?));
            *time = start.elapsed().as_nanos();
        }
        writeln!(out, "ACCEPTED\t{hash:016x}")?;
        for elapsed in times {
            writeln!(out, "SAMPLE\t{elapsed}")?;
        }
    }
    out.flush()?;
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("native comparison failed: {error}");
        std::process::exit(1);
    }
}
