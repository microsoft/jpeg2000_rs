use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{hint::black_box, time::Instant};

#[cfg(any(
    all(feature = "current", feature = "release022"),
    all(feature = "current", feature = "hayro-scalar"),
    all(feature = "release022", feature = "hayro-scalar"),
    not(any(feature = "current", feature = "release022", feature = "hayro-scalar"))
))]
compile_error!("select exactly one decoder feature");

#[cfg(feature = "current")]
use decoder_current as decoder;
#[cfg(feature = "release022")]
use decoder_release as decoder;

fn digest(data: &[u8]) -> String {
    format!("{:x}", Sha256::digest(data))
}

#[cfg(any(feature = "current", feature = "release022"))]
fn decode(data: &[u8], raw: bool) -> (Value, u128) {
    use decoder::{DecodeOptions, TypedSamples};
    let start = Instant::now();
    let result = if raw {
        decoder::decode_codestream(black_box(data), &DecodeOptions::default())
    } else {
        decoder::decode_jp2(black_box(data), &DecodeOptions::default())
    };
    let elapsed = start.elapsed().as_nanos();
    let outcome = match result {
        Err(error) => json!({"status": "error", "error": format!("{error:?}")}),
        Ok(image) => {
            let mut canonical = Sha256::new();
            let mut components = Vec::new();
            let mut planes = Vec::new();
            for component in image.components() {
                let mut bytes = Vec::new();
                let mut u8_plane = Vec::new();
                let mut fits_u8 = true;
                let signed = matches!(component.samples(), TypedSamples::Signed(_));
                match component.samples() {
                    TypedSamples::Unsigned(samples) => {
                        for sample in samples {
                            bytes.extend_from_slice(&sample.to_le_bytes());
                            if let Ok(value) = u8::try_from(*sample) {
                                u8_plane.push(value);
                            } else {
                                fits_u8 = false;
                            }
                        }
                    }
                    TypedSamples::Signed(samples) => {
                        for sample in samples {
                            bytes.extend_from_slice(&sample.to_le_bytes());
                            if let Ok(value) = u8::try_from(*sample) {
                                u8_plane.push(value);
                            } else {
                                fits_u8 = false;
                            }
                        }
                    }
                }
                canonical.update(component.width().to_le_bytes());
                canonical.update(component.height().to_le_bytes());
                canonical.update([u8::from(signed)]);
                canonical.update(&bytes);
                components.push(
                    json!({"width": component.width(), "height": component.height(),
                                       "signed": signed, "sha256_le64": digest(&bytes)}),
                );
                planes.push(if fits_u8 { Some(u8_plane) } else { None });
            }
            let pixels = image.width() as usize * image.height() as usize;
            let interleaved = if planes
                .iter()
                .all(|p| p.as_ref().is_some_and(|p| p.len() == pixels))
            {
                let mut bytes = Vec::with_capacity(pixels * planes.len());
                for i in 0..pixels {
                    for plane in &planes {
                        bytes.push(plane.as_ref().unwrap()[i]);
                    }
                }
                Some(digest(&bytes))
            } else {
                None
            };
            json!({"status": "ok", "width": image.width(), "height": image.height(),
                   "channels": components.len(), "components": components,
                   "samples_sha256_le64": format!("{:x}", canonical.finalize()),
                   "samples_sha256_u8_interleaved": interleaved})
        }
    };
    (outcome, elapsed)
}

#[cfg(feature = "hayro-scalar")]
fn decode(data: &[u8], _raw: bool) -> (Value, u128) {
    let start = Instant::now();
    let decoded =
        hayro_jpeg2000::Image::new(black_box(data), &hayro_jpeg2000::DecodeSettings::default())
            .and_then(|image| {
                let width = image.width();
                let height = image.height();
                let channels = image.color_space().num_channels() + u8::from(image.has_alpha());
                image
                    .decode()
                    .map(|pixels| (width, height, channels, pixels))
            });
    let elapsed = start.elapsed().as_nanos();
    let outcome = match decoded {
        Ok((width, height, channels, pixels)) => {
            assert_eq!(
                pixels.len(),
                width as usize * height as usize * channels as usize
            );
            json!({"status": "ok", "width": width, "height": height, "channels": channels,
                   "samples_sha256_u8_interleaved": digest(&pixels)})
        }
        Err(error) => json!({"status": "error", "error": format!("{error:?}")}),
    };
    (outcome, elapsed)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(
        args.len(),
        3,
        "usage: jpeg2000-final-consumer-bench INPUT ITERATIONS"
    );
    let data = std::fs::read(&args[1]).expect("read input");
    let raw = args[1].ends_with(".j2k");
    let iterations: usize = args[2].parse().expect("iterations");
    assert!(iterations > 0);
    let mut measurements = Vec::new();
    let mut reference = None;
    for _ in 0..iterations {
        let (outcome, elapsed) = decode(&data, raw);
        if let Some(previous) = &reference {
            assert_eq!(
                previous, &outcome,
                "non-deterministic output within process"
            );
        }
        reference = Some(outcome);
        measurements.push(elapsed);
    }
    println!(
        "{}",
        json!({"input_sha256": digest(&data), "decode_ns": measurements,
                         "outcome": reference.unwrap()})
    );
}
