# jpeg2000-image

An experimental companion [`image`](https://crates.io/crates/image) 0.25
adapter for [`jpeg2000-decoder`](https://crates.io/crates/jpeg2000-decoder).
Requires Rust 1.88. No Verus installation or native decoder library is needed.
This workspace member is not published; it does not change the decoder's
default features, executable implementation, specifications or proof scope.
It is a separate crate, not an optional feature of the decoder.

Development builds use the workspace 0.2 decoder. A packaged adapter resolves
the declared registry dependency (0.1.x or 0.2.x); it uses the API subset shared
by these lines. This keeps packaging possible before the separately authorized
0.2 publication. CI tests the workspace and packaged registry boundaries.
The root workspace defaults to the decoder alone;
select `-p jpeg2000-image` to build this companion.

For a local application, use path dependencies on this directory and the same
`image` 0.25 release. No changes to the `image` crate itself are necessary.

## Decode directly

```no_run
use image::DynamicImage;
use jpeg2000_image::Jpeg2000Decoder;

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let file = std::fs::File::open("input.jp2")?;
let image = DynamicImage::from_decoder(Jpeg2000Decoder::new(file)?)?;
println!("{:?}", image.color());
# Ok(())
# }
```

Output is always normalized U16: `L16`, `La16`, `Rgb16`, or `Rgba16`.
Eight-bit samples therefore become full-range U16, not low-valued unscaled U16.
This is a display-image API, not exact preservation of arbitrary signed or
greater-than-16-bit integer samples. `original_color_type` uses `image`'s
default (the converted output type), not a claim about encoded precision.

## Register with image

```no_run
use jpeg2000_image::{DecoderOptions, register_decoding_hooks};

# fn main() -> Result<(), Box<dyn std::error::Error>> {
register_decoding_hooks(DecoderOptions::default())?;
let image = image::ImageReader::open("input.jp2")?.decode()?;
# Ok(())
# }
```

Registration enables `.jp2`, `.j2k`, `.j2c`, and `.jpc` plus JP2 and raw
codestream signature detection. `ImageReader::with_guessed_format` and
`image::load_from_memory` use those detection hooks.
There is no JPEG 2000 variant in `image::ImageFormat`: `ImageReader::format()`
can return `None` for a registered external format even though `decode()` works.
Do not use that getter as an external-codec capability check.
Call once at startup, before other JPEG 2000 adapters: `image` hooks are
process-global, first-registration-wins, and cannot be unregistered.
Conflicts are errors; multi-extension registration cannot be atomic against
concurrent competing registrations. Direct construction avoids global state.

Raw codestreams have no container color declaration. Explicitly choose
`DecoderOptions { raw_color_space: Some(RawColorSpace::Srgb), ..Default::default() }`
for three decoded sRGB components, or `RawColorSpace::Grayscale` for one.
The default rejects untagged raw input instead of guessing from component count.
Hook options apply to all images decoded through those hooks; use direct
construction for per-image policies.

## Initial scope

- Single-codestream JP2 with enumerated grayscale, sRGB, or sYCC.
- Color conversion, subsampling, palette and channel mappings use the core codec.
- At most one straight, whole-image alpha channel.
- Explicitly colored raw JPEG 2000 codestreams.
- No ICC color management, CMYK conversion, premultiplied/component-associated
  alpha, JPX composition, JPH containers, JPIP, or encoding.
- Unsupported inputs return errors. There is no fallback to another decoder.

## Limits

Construction reads compressed input, with a cap from
`DecoderOptions::limits.maximum_input_bytes()` (plus one stack-buffered probe
byte for overflow detection), and performs codec-bounded inspection without decoding pixels.
Configure smaller input/metadata/work caps **before construction** for untrusted
input: the core's default compressed-input cap is 2 GiB, not `image`'s 512 MiB
default allocation budget. Header inspection validates container/codestream dimensions.

`ImageDecoder::set_limits` checks strict dimensions before pixel decoding.
`ImageReader` calls it after construction; its limits cannot retroactively
constrain compressed buffering or header inspection. For `image` 0.25.10,
`ImageReader::decode` reserves its output before passing the remaining memory
budget to the decoder. The adapter deducts its compressed-buffer capacity and
tightens the codec's decoded-byte cap from that remainder, without reserving
the caller-owned output twice.

Allocation limits are best-effort, not a measured peak-RSS guarantee or a
replacement for process isolation. Codec caps are stage-specific and exclude
allocator overhead. Direct `DynamicImage::from_decoder` does not install an
`ImageReader` allocation budget: configure codec limits and call `set_limits`
with the budget remaining after allocating your own output if needed.
Disabling `image` limits does not disable codec resource caps.

## Validation

The committed 9x7 synthetic fixtures cover grayscale/RGB, straight alpha,
U8-to-U16 normalization, native U16 endpoints, raw codestreams, nonzero origins,
multiple tiles, palette mappings, channel permutations, and neutral sYCC.
`tests/fixtures/generate.py` reproduces them with Pillow 13.0.0 / OpenJPEG 2.5.4:

```sh
python -m pip install Pillow==13.0.0
python tests/fixtures/generate.py
```

Expected samples come from the original synthetic patterns, not this decoder.
The generator round-trips the fixtures through Pillow/OpenJPEG. For the cdef
permutation, Pillow preserves physical component order; its round-trip checks
those physical samples, while the expected rendered samples follow the explicit
JP2 channel associations. This case is not an independent rendered-color oracle.
The fixtures are synthetic test data contributed under this crate's MIT license.
Pillow is only needed to regenerate them, not to run the Rust tests.

```sh
cargo +1.88.0 test -p jpeg2000-image --all-targets --locked
cargo +1.88.0 test -p jpeg2000-image --doc --locked
cargo +1.88.0 check -p jpeg2000-image --release --all-targets --locked
cargo fmt -p jpeg2000-image -- --check
cargo clippy -p jpeg2000-image --all-targets --locked -- -D warnings
```

The repository-pinned development formatter is separate from the runtime MSRV.
The existing `validation/image-consumer-probe` remains an independent,
intentionally narrower consumer of the actual unpacked decoder package; this
companion does not replace or redirect that packaging gate.

This adapter is experimental. No performance, official conformance, or
completed formal-verification claim is made.
The decoder dependency's third-party BSD table notices must also be retained
when redistributing its code or relevant binaries.
