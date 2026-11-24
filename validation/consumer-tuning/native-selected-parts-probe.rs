use codec::{decode_codestream_selected, DecodeOptions, DecodeSelection, ImageRegion};
use std::{env, fs, hint::black_box, process::ExitCode, time::Instant};

#[global_allocator]
static ALLOCATOR: std::alloc::System = std::alloc::System;

const ITERATIONS: u128 = 512;
const WARMUPS: u8 = 2;

fn expected(roi: bool) -> String {
    let (x, width) = if roi { (31, 1) } else { (0, 32) };
    let samples = vec![128_u64; width];
    format!(
        "TypedImage {{ width: {width}, height: 1, x_origin: {x}, y_origin: 0, components: [TypedComponent {{ width: {width}, height: 1, info: ComponentInfo {{ precision: 8, signed: false, x_subsampling: 1, y_subsampling: 1, x_registration: 0, y_registration: 0 }}, samples: Unsigned({samples:?}), channel_definitions: [] }}] }}"
    )
}

fn check(roi: bool, actual: &str) -> Result<(), String> {
    let expected = expected(roi);
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "selected output differs:\nexpected {expected}\nactual   {actual}"
        ))
    }
}

fn self_check() -> Result<(), String> {
    let roi = expected(true);
    check(true, &roi)?;
    for incorrect in [
        roi.replace("Unsigned([128])", "Unsigned([129])"),
        roi.replace("x_subsampling: 1", "x_subsampling: 2"),
        roi.replace(
            "channel_definitions: []",
            "channel_definitions: [ChannelDefinition { channel_type: Color, association: Color(1) }]",
        ),
        expected(false),
    ] {
        if check(true, &incorrect).is_ok() {
            return Err("self-check accepted incorrect output".into());
        }
    }
    println!("SELF-CHECK\tPASS");
    Ok(())
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args == ["self-check"] {
        return Ok(self_check()?);
    }
    let [operation, mode, path] = args.as_slice() else {
        return Err(
            "usage: jpeg2000-selected-probe <preflight|bench-fixed> <full|roi> FILE | self-check"
                .into(),
        );
    };
    let roi = match mode.as_str() {
        "full" => false,
        "roi" => true,
        _ => return Err("expected full or roi".into()),
    };
    if !matches!(operation.as_str(), "preflight" | "bench-fixed") {
        return Err("expected preflight or bench-fixed".into());
    }
    let data = fs::read(path)?;
    let options = DecodeOptions::default();
    let mut selection = DecodeSelection::full_image().with_discard_levels(0);
    if roi {
        selection = selection.with_region(ImageRegion::new(31, 0, 1, 1));
    }
    let decode = || decode_codestream_selected(black_box(&data), &options, &selection);
    // The first untimed decode also verifies all returned fields; never walk samples in the clocked loop.
    let snapshot = format!("{:?}", decode()?);
    check(roi, &snapshot)?;
    if operation == "preflight" {
        println!("{snapshot}");
        return Ok(());
    }
    for _ in 1..WARMUPS {
        drop(black_box(decode()?));
    }
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        drop(black_box(decode()?));
    }
    let elapsed_ns = start.elapsed().as_nanos();
    println!("BATCH\t{ITERATIONS}\t{WARMUPS}\t{elapsed_ns}");
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("selected probe failed: {error}");
            ExitCode::FAILURE
        }
    }
}
