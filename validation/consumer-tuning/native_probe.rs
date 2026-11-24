#![forbid(unsafe_code)]

use codec::image::{ChannelAssociation, ChannelType, DecodedImage};
use codec::{DecodeOptions, TypedImage, TypedSamples, decode_codestream_reconstructed, decode_jp2};
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

fn typed_words(image: &TypedImage, mut word: impl FnMut(u64) -> io::Result<()>) -> io::Result<()> {
    for value in [
        2, // mapped typed planes, including channel definitions
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
        let (signed, count) = match component.samples() {
            TypedSamples::Signed(samples) => (1, samples.len()),
            TypedSamples::Unsigned(samples) => (0, samples.len()),
        };
        for value in [
            u64::from(component.width()),
            u64::from(component.height()),
            u64::from(info.precision),
            u64::from(info.signed),
            u64::from(info.x_subsampling),
            u64::from(info.y_subsampling),
            u64::from(info.x_registration),
            u64::from(info.y_registration),
            signed,
            count as u64,
            component.channel_definitions().len() as u64,
        ] {
            word(value)?;
        }
        for definition in component.channel_definitions() {
            word(match definition.channel_type() {
                ChannelType::Color => 0,
                ChannelType::Opacity => 1,
                ChannelType::PremultipliedOpacity => 2,
                ChannelType::Unspecified => 65535,
            })?;
            word(match definition.association() {
                ChannelAssociation::WholeImage => 0,
                ChannelAssociation::Color(index) => u64::from(index),
                ChannelAssociation::Unassociated => 65535,
            })?;
        }
        match component.samples() {
            TypedSamples::Signed(samples) => {
                for &sample in samples {
                    word(sample as u64)?;
                }
            }
            TypedSamples::Unsigned(samples) => {
                for &sample in samples {
                    word(sample)?;
                }
            }
        }
    }
    Ok(())
}

fn sample<T>(
    dump: bool,
    decode: impl Fn() -> Result<T, codec::DecodeError>,
    serialize: impl Fn(&T, &mut dyn FnMut(u64) -> io::Result<()>) -> io::Result<()>,
) -> Result<(), Box<dyn Error>> {
    let first = decode()?;
    let mut out = io::BufWriter::new(io::stdout().lock());
    if dump {
        serialize(&first, &mut |v| out.write_all(&v.to_le_bytes()))?;
    } else {
        let mut hash = 14_695_981_039_346_656_037_u64;
        serialize(&first, &mut |v| {
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

fn run() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [operation, path] = args.as_slice() else {
        return Err("usage: native-probe <dump|bench|dump-jp2|bench-jp2> INPUT".into());
    };
    let data = fs::read(path)?;
    let options = DecodeOptions::default();
    match operation.as_str() {
        "dump" | "bench" => sample(
            operation == "dump",
            || decode_codestream_reconstructed(black_box(&data), &options),
            |image, word| native_words(image, word),
        ),
        "dump-jp2" | "bench-jp2" => sample(
            operation == "dump-jp2",
            || decode_jp2(black_box(&data), &options),
            |image, word| typed_words(image, word),
        ),
        _ => Err("invalid operation".into()),
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("native comparison failed: {error}");
        std::process::exit(1);
    }
}
