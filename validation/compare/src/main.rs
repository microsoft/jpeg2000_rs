use std::{
    env, fs,
    hint::black_box,
    io::{BufWriter, Write},
    path::Path,
    process,
    time::Instant,
};

use jpeg2000_rs::{DecodeOptions, TypedImage, TypedSamples};
use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct Component {
    width: u32,
    height: u32,
    precision: u8,
    signed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct Layout {
    width: u32,
    height: u32,
    components: Vec<Component>,
}

struct Frame {
    layout: Layout,
    samples: Vec<i64>,
}

#[derive(Debug)]
struct Failure {
    status: &'static str,
    decoder_accepted: bool,
    unsupported: bool,
    detail: String,
}

impl Failure {
    fn normalization(detail: &str) -> Self {
        Self {
            status: "not-comparable",
            decoder_accepted: true,
            unsupported: false,
            detail: detail.to_owned(),
        }
    }

    fn internal(detail: String) -> Self {
        Self {
            status: "harness-error",
            decoder_accepted: true,
            unsupported: false,
            detail,
        }
    }
}

#[derive(Serialize)]
struct Timing {
    decode_ns: u128,
    common_output_ns: u128,
}

#[derive(Serialize)]
struct Observation {
    schema_version: u8,
    engine: String,
    hayro_version: &'static str,
    hayro_features: &'static str,
    lifecycle: &'static str,
    status: &'static str,
    decoder_accepted: bool,
    unsupported: bool,
    layout: Option<Layout>,
    sample_count: usize,
    output_sha256: Option<String>,
    timings: Vec<Timing>,
    error: Option<String>,
}

fn component_area(width: u32, height: u32) -> Result<usize, Failure> {
    let area = u64::from(width) * u64::from(height);
    if area == 0 || area > 16_777_216 {
        return Err(Failure::normalization(
            "comparison component area is outside its bounded profile",
        ));
    }
    usize::try_from(area).map_err(|_| Failure::normalization("component area does not fit usize"))
}

fn normalize_ours(image: &TypedImage) -> Result<Frame, Failure> {
    let mut components = Vec::new();
    let mut samples = Vec::new();
    for component in image.components() {
        let info = component.info();
        if info.signed || !(1..=16).contains(&info.precision) {
            return Err(Failure::normalization(
                "common comparison profile requires unsigned components with precision 1..16",
            ));
        }
        let count = component_area(component.width(), component.height())?;
        let TypedSamples::Unsigned(values) = component.samples() else {
            return Err(Failure::normalization(
                "expected unsigned component storage",
            ));
        };
        if values.len() != count {
            return Err(Failure::normalization(
                "component samples disagree with geometry",
            ));
        }
        let peak = (1_u64 << info.precision) - 1;
        for value in values {
            if *value > peak {
                return Err(Failure::normalization("sample exceeds component precision"));
            }
            samples.push(
                i64::try_from(*value).map_err(|_| Failure::normalization("sample overflow"))?,
            );
        }
        components.push(Component {
            width: component.width(),
            height: component.height(),
            precision: info.precision,
            signed: false,
        });
    }
    if components.is_empty() {
        return Err(Failure::normalization("decoded image has no components"));
    }
    Ok(Frame {
        layout: Layout {
            width: image.width(),
            height: image.height(),
            components,
        },
        samples,
    })
}

fn normalize_hayro(
    image: &hayro_jpeg2000::DecodedImage<'_>,
    width: u32,
    height: u32,
) -> Result<Frame, Failure> {
    let count = component_area(width, height)?;
    let mut components = Vec::new();
    let mut samples = Vec::new();
    for component in image.components() {
        let precision = component.bit_depth();
        if !(1..=16).contains(&precision) || component.samples().len() != count {
            return Err(Failure::normalization(
                "hayro components are outside the unsigned, full-grid precision 1..16 comparison profile",
            ));
        }
        let peak = (1_u32 << precision) - 1;
        for value in component.samples() {
            if !value.is_finite() {
                return Err(Failure::normalization(
                    "hayro returned a non-finite component sample",
                ));
            }
            samples.push(value.round().clamp(0.0, peak as f32) as i64);
        }
        components.push(Component {
            width,
            height,
            precision,
            signed: false,
        });
    }
    if components.is_empty() {
        return Err(Failure::normalization("decoded image has no components"));
    }
    Ok(Frame {
        layout: Layout {
            width,
            height,
            components,
        },
        samples,
    })
}

fn decode_once(engine: &str, format: &str, data: &[u8]) -> Result<(Frame, Timing), Failure> {
    let start = Instant::now();
    let frame;
    let decode_ns;
    match engine {
        "ours" => {
            let options = DecodeOptions::default();
            let image = match format {
                "raw" => jpeg2000_rs::decode_codestream(data, &options),
                "jp2" => jpeg2000_rs::decode_jp2(data, &options),
                "jph" => jpeg2000_rs::decode_jph(data, &options),
                "jpx" => jpeg2000_rs::decode_jpx_codestream(data, 0, &options),
                _ => unreachable!("format checked before decoding"),
            }
            .map_err(|error| Failure {
                status: "rejected",
                decoder_accepted: false,
                unsupported: matches!(
                    error,
                    jpeg2000_rs::DecodeError::UnsupportedFeature { .. }
                        | jpeg2000_rs::DecodeError::UnsupportedProfile { .. }
                ),
                detail: format!("{error:?}: {error}"),
            })?;
            black_box(&image);
            decode_ns = start.elapsed().as_nanos();
            frame = normalize_ours(&image)?;
        }
        "hayro" => {
            let settings = hayro_jpeg2000::DecodeSettings::default();
            let image = hayro_jpeg2000::Image::new(data, &settings).map_err(hayro_failure)?;
            let mut context = hayro_jpeg2000::DecoderContext::default();
            let decoded = image.decode(&mut context).map_err(hayro_failure)?;
            black_box(&decoded);
            decode_ns = start.elapsed().as_nanos();
            frame = normalize_hayro(&decoded, image.width(), image.height())?;
        }
        _ => unreachable!("engine checked before decoding"),
    }
    // Native images and decoder contexts are dropped before the inclusive timer.
    let common_output_ns = start.elapsed().as_nanos();
    black_box(&frame);
    Ok((
        frame,
        Timing {
            decode_ns,
            common_output_ns,
        },
    ))
}

fn hayro_failure(error: hayro_jpeg2000::DecodeError) -> Failure {
    use hayro_jpeg2000::{DecodeError, FormatError, MarkerError};
    Failure {
        status: "rejected",
        decoder_accepted: false,
        unsupported: matches!(
            error,
            DecodeError::Marker(MarkerError::Unsupported)
                | DecodeError::Format(FormatError::Unsupported)
        ),
        detail: format!("{error:?}: {error}"),
    }
}

fn frame_digest(frame: &Frame) -> Result<String, Failure> {
    let mut hash = Sha256::new();
    hash.update(b"jpeg2000-comparison-v1\0");
    hash.update(frame.layout.width.to_le_bytes());
    hash.update(frame.layout.height.to_le_bytes());
    hash.update(
        u32::try_from(frame.layout.components.len())
            .map_err(|error| Failure::internal(format!("component count overflow: {error}")))?
            .to_le_bytes(),
    );
    for component in &frame.layout.components {
        hash.update(component.width.to_le_bytes());
        hash.update(component.height.to_le_bytes());
        hash.update([component.precision, u8::from(component.signed)]);
    }
    for value in &frame.samples {
        hash.update(value.to_le_bytes());
    }
    Ok(format!("{:x}", hash.finalize()))
}

fn write_frame(path: &Path, frame: &Frame) -> std::io::Result<()> {
    let mut file = BufWriter::new(fs::File::create(path)?);
    for value in &frame.samples {
        file.write_all(&value.to_le_bytes())?;
    }
    file.flush()
}

fn run() -> Result<bool, Box<dyn std::error::Error>> {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 6
        || !matches!(args[1].as_str(), "ours" | "hayro")
        || !matches!(args[2].as_str(), "raw" | "jp2" | "jph" | "jpx")
    {
        return Err("usage: jpeg2000-comparison <ours|hayro> <raw|jp2|jph|jpx> <input> <output-i64le> <iterations>".into());
    }
    let iterations = args[5].parse::<usize>()?;
    if !(1..=100).contains(&iterations) {
        return Err("iterations must be in 1..100".into());
    }
    if fs::metadata(&args[3])?.len() > 64 << 20 {
        return Err("comparison input exceeds 64 MiB".into());
    }
    let data = fs::read(&args[3])?;
    let mut observation = Observation {
        schema_version: 1,
        engine: args[1].clone(),
        hayro_version: "0.4.1",
        hayro_features: if cfg!(feature = "default") {
            "published-defaults"
        } else if cfg!(feature = "scalar") {
            "std-only"
        } else {
            "no-defaults"
        },
        lifecycle: "fresh image/context per iteration; input I/O and hashing excluded",
        status: "decoded",
        decoder_accepted: true,
        unsupported: false,
        layout: None,
        sample_count: 0,
        output_sha256: None,
        timings: Vec::new(),
        error: None,
    };
    // One untimed decode warms code/allocator caches, but no decoder state is reused.
    let result = (|| -> Result<(), Failure> {
        let (warmup, _) = decode_once(&args[1], &args[2], &data)?;
        drop(warmup);
        for iteration in 0..iterations {
            let (frame, timing) = decode_once(&args[1], &args[2], &data)?;
            let hash = frame_digest(&frame)?;
            if let Some(previous) = &observation.output_sha256
                && (previous != &hash || observation.layout.as_ref() != Some(&frame.layout))
            {
                return Err(Failure::internal(
                    "successive decodes returned different output".to_owned(),
                ));
            }
            if iteration == 0 {
                write_frame(Path::new(&args[4]), &frame).map_err(|error| {
                    Failure::internal(format!("cannot write comparison samples: {error}"))
                })?;
                observation.sample_count = frame.samples.len();
                observation.layout = Some(frame.layout.clone());
                observation.output_sha256 = Some(hash);
            }
            observation.timings.push(timing);
        }
        Ok(())
    })();
    if let Err(error) = result {
        observation.status = error.status;
        observation.decoder_accepted = error.decoder_accepted;
        observation.unsupported = error.unsupported;
        observation.error = Some(error.detail);
    }
    println!("{}", serde_json::to_string(&observation)?);
    Ok(observation.status == "decoded")
}

fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => process::exit(1),
        Err(error) => {
            eprintln!("{error}");
            process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_adapters_materialize_the_same_minimal_image() {
        let data = include_bytes!("../../generated/corpus/raw-minimal.j2k");
        let (ours, ours_time) = decode_once("ours", "raw", data).unwrap();
        let (hayro, hayro_time) = decode_once("hayro", "raw", data).unwrap();
        assert_eq!(ours.samples, vec![128]);
        assert_eq!(ours.layout, hayro.layout);
        assert_eq!(frame_digest(&ours).unwrap(), frame_digest(&hayro).unwrap());
        assert!(ours_time.common_output_ns >= ours_time.decode_ns);
        assert!(hayro_time.common_output_ns >= hayro_time.decode_ns);
    }

    #[test]
    fn canonical_hash_binds_layout_precision_and_samples() {
        let mut frame = Frame {
            layout: Layout {
                width: 2,
                height: 1,
                components: vec![Component {
                    width: 2,
                    height: 1,
                    precision: 8,
                    signed: false,
                }],
            },
            samples: vec![0, 255],
        };
        let original = frame_digest(&frame).unwrap();
        frame.samples[1] = 254;
        assert_ne!(original, frame_digest(&frame).unwrap());
        frame.samples[1] = 255;
        frame.layout.components[0].precision = 16;
        assert_ne!(original, frame_digest(&frame).unwrap());
    }
}
