#![forbid(unsafe_code)]

use jpeg2000_decoder::{
    DecodeOptions, DecodeSelection, ImageRegion, TypedImage, TypedSamples,
    decode_codestream_selected,
};
use std::{
    env,
    error::Error,
    fs,
    hint::black_box,
    io::{self, Write},
    time::{Duration, Instant},
};

fn dump(image: &TypedImage) -> io::Result<()> {
    let mut out = io::BufWriter::new(io::stdout().lock());
    let mut word = |value: u64| out.write_all(&value.to_le_bytes());
    word(u64::from(image.width()))?;
    word(u64::from(image.height()))?;
    word(image.components().len() as u64)?;
    for component in image.components() {
        let info = component.info();
        for value in [
            u64::from(component.width()),
            u64::from(component.height()),
            u64::from(info.precision),
            u64::from(info.signed),
        ] {
            word(value)?;
        }
        match component.samples() {
            TypedSamples::Unsigned(samples) => {
                for &sample in samples {
                    word(sample)?;
                }
            }
            TypedSamples::Signed(samples) => {
                for &sample in samples {
                    word(sample as u64)?;
                }
            }
        }
    }
    out.flush()
}

fn run() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [path, mode, reduce, window, iterations, minimum_ms, warmups] = args.as_slice() else {
        return Err("usage: bench-vs-openjpeg INPUT typed|native|dump REDUCE x,y,w,h|- ITERATIONS MINIMUM_MS WARMUPS".into());
    };
    if !matches!(mode.as_str(), "typed" | "native" | "dump") {
        return Err("unknown output mode".into());
    }
    let iterations: usize = iterations.parse()?;
    let warmups: usize = warmups.parse()?;
    let minimum = Duration::from_millis(minimum_ms.parse()?);
    if iterations == 0 {
        return Err("at least one measured iteration is required".into());
    }
    let mut selection = DecodeSelection::default().with_discard_levels(reduce.parse()?);
    if window != "-" {
        let values = window
            .split(',')
            .map(str::parse)
            .collect::<Result<Vec<u32>, _>>()?;
        let [x, y, width, height] = values.as_slice() else {
            return Err("window must be x,y,width,height".into());
        };
        selection = selection.with_region(ImageRegion::new(*x, *y, *width, *height));
    }
    let input = fs::read(path)?;
    let options = DecodeOptions::default();
    let decode = || decode_codestream_selected(black_box(&input), &options, &selection);
    if mode == "dump" {
        return Ok(dump(&decode()?)?);
    }
    for _ in 0..warmups {
        drop(black_box(decode()?));
    }
    let mut times = Vec::new();
    let mut total = Duration::ZERO;
    while times.len() < iterations || total < minimum {
        let start = Instant::now();
        let image = black_box(decode()?);
        let elapsed = start.elapsed();
        drop(image);
        total += elapsed;
        times.push(elapsed.as_nanos());
    }
    for elapsed in times {
        println!("SAMPLE\t{elapsed}");
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("benchmark failed: {error}");
        std::process::exit(1);
    }
}
