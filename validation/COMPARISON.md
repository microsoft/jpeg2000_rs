# Comparing with hayro-jpeg2000

The optional comparison calls the unmodified production decoder and the
published **hayro-jpeg2000 0.4.1** crate. It does not add dependencies to the
production crate, vendor another decoder, or replace the single-source Verus
architecture.

## Reproduce

Use the [validation prerequisites](VALIDATION.md), including GNU Time on Linux,
OpenJPEG and the pinned scalar OpenJPH tools.

```sh
python validation/run-validation.py compare-hayro
python validation/run-validation.py compare-hayro --capabilities-only --iterations 1 --repetitions 1
cargo test --manifest-path validation/compare/Cargo.toml --locked
cargo test --manifest-path validation/compare/Cargo.toml --locked --no-default-features --features scalar
```

The separate [comparison manifest](compare/Cargo.toml) pins hayro to `=0.4.1`;
its lockfile binds transitive dependencies. The published archive checksum is
`122c5f834c37a2260b9c851bb8be685cf539b2a8b94b704a931ef7d2525d5835`
and its recorded source revision is
`ea9c81dc70cde40c64205986fdcfcd481fe934d8`.
The default build enables hayro's published defaults. The additional scalar
build enables `std` without the SIMD/image defaults; report these separately.
Do not describe the default build as unsafe-free throughout its dependency
graph: hayro documents that its optional SIMD dependency uses unsafe.

`hayro-comparison.json` and any `comparison-failures/` inputs are generated
under ignored `target/validation/`, never committed source snapshots.
`--output-dir`, `--iterations` and `--repetitions` select a report location and
bounded sample counts. Missing default tools block execution; configured
missing tools are errors.

## Timing and output semantics

The canonical corpus, generated numerical matrix and larger performance
workloads are distinct report sections. A corpus metadata inspection or JPIP
ingestion operation is not compared with an unrelated image-decoding API.
No-equivalent-API results are explicit.

For generated unsigned 8/16-bit grayscale/RGB inputs, independent
OpenJPEG/OpenJPH output qualifies each decoder before timing. A lossless
reference must first reproduce the original source exactly. The benchmark
does not accept a faulty reference roundtrip as a new expected image.

Both adapters produce the same canonical layout and planar `i64` sample
representation. Ours retains its typed integer samples. Hayro's exposed `f32`
components are rounded and clipped to the declared unsigned range. This is
an explicitly bounded comparison profile, not a claim that float components
preserve every larger-precision integer or signedness.

- **Decode-only time** includes header parsing, decoding and allocation. Native
  output representations differ, so this is a diagnostic, not the primary
  apples-to-apples result.
- **Common-output time** additionally includes conversion to the shared planar
  representation and disposal of native image/context state.
- Input file I/O, hashing, sample-file writes and JSON serialization are outside
  those timers. `black_box` and hash-bound sample validation keep outputs live.
- Each measured decode uses a fresh image/context. One untimed decode warms
  code/allocator caches. Hayro's reusable `Image`/`DecoderContext` lifecycle is
  not measured here; do not present these as reusable-context throughput.
- The default performance run uses three process repetitions with five timed
  decodes each. GNU Time records whole-process peak RSS, including input,
  warmup, canonical output and observation work, not decoder allocations alone.
- Both processes share the same Rust compiler, release profile, inputs and
  external limits: one-GiB address space, 64-MiB files, one-MiB captured output,
  and a bounded process timeout. Build commands, compiler/environment,
  executable, input, output and comparison-source hashes are recorded.

Unsupported cases have no speed ratio. Lossy outputs can qualify within their
declared engineering budgets without being byte-identical; the report preserves
both reference-error metrics and exact-output flags. These budgets are not
official Part 4 tolerances. Default-mode malformed-input acceptance differences
describe policy observations, not a vulnerability or conformance verdict.

Do not infer general performance from one generated workload, average
unsupported-feature rejections into speed scores, or treat the HT-heavy matrix
as an unbiased feature-coverage percentage. Repeat on representative application
inputs and profile measured bottlenecks before changing production algorithms.

## Version-specific feature/API matrix

**D** means documented, **S** source-inspected, and **T** exercised by this
comparison or the linked decoder tests. These are different evidence levels;
none is an ISO/IEC certification.

| Surface | jpeg2000_rs | hayro-jpeg2000 0.4.1 |
|---|---|---|
| Raw codestream and JP2 | Typed component decoding (D/T) | Published `Image` API (D/T) |
| HTJ2K/JPH | Selected cleanup/refinement and mixed-routing implementation; generated HT tests (D/T) | No advertised HT decoder; generated HT probes return unsupported-marker outcomes (S/T) |
| JPX | Explicit codestream/layer/frame selection and bounded composition (D/T) | Minimal single-codestream JPX wrapper acceptance is observed; no dedicated layer/frame/composition API is exposed (S/T) |
| JPIP | Message parsing, sparse cache, reconstruction and progressive APIs; no network transport (D/T) | No equivalent published JPIP API (D/S) |
| Part 2 coding extensions | Selected MCT/DFS/ADS/ATK/NLT/CBD support, not every extension (D) | Documentation claims core coding and some extension color spaces, not the same extension set (D) |
| Native sample API | Signed/unsigned typed integer components, declared precision 1..38; broader independent qualification remains necessary (D) | Component `f32` samples and bit-depth accessors; parser precision ceiling is 31 (S); 8/16-bit unsigned cases are compared (T) |
| Signedness | Retained in component metadata (D) | The SIZ sign flag is read but not retained by that parser; signedness-preservation is not qualified here (S) |
| Selection | Absolute regions, tiles/rectangular tile sets and explicit native discard levels (D/T) | `target_resolution` hint; no equivalent public region/tile-set selector (D/S) |
| Color/API integration | Enumerated sRGB/grayscale/sYCC conversion; ICC retained without execution (D) | RGB/grayscale/CMYK/ICC color-space API and optional `image`/`moxcms` integration (D/S); not timed in this common-component workload |
| Reusable decoder context | No equivalent reusable context in the compared top-level API (S) | Public `DecoderContext` and reusable parsed `Image` (D/S) |
| SIMD and `no_std` | No explicit SIMD backend or `no_std` interface; LLVM optimization is not ruled out (S) | Optional SIMD, enabled by default; allocator-backed `no_std` documented (D) |
| Resource policy | Configurable typed resource limits, plus separately measured process budgets (D/T) | Internal validation; published settings are not an equivalent configurable resource-budget API (D/S) |
| Formal guarantees | Bounds, termination and selected functional contracts, not full parser-to-pixel correctness (D) | Published safety/testing claims, not a Verus or complete conformance claim (D) |

### Evidence

- [Published crate/API documentation](https://docs.rs/hayro-jpeg2000/0.4.1/hayro_jpeg2000/)
- [Pinned API/settings/component source](https://github.com/LaurenzV/hayro/blob/ea9c81dc70cde40c64205986fdcfcd481fe934d8/hayro-jpeg2000/src/lib.rs)
- [Pinned codestream parser](https://github.com/LaurenzV/hayro/blob/ea9c81dc70cde40c64205986fdcfcd481fe934d8/hayro-jpeg2000/src/j2c/codestream.rs)
- [Pinned bitplane representation](https://github.com/LaurenzV/hayro/blob/ea9c81dc70cde40c64205986fdcfcd481fe934d8/hayro-jpeg2000/src/j2c/bitplane.rs)
- [Pinned optional image/color integration](https://github.com/LaurenzV/hayro/blob/ea9c81dc70cde40c64205986fdcfcd481fe934d8/hayro-jpeg2000/src/integration.rs)
- [Our supported profile](../SUPPORTED.md), [proof boundary](../PROOFS.md), and
  [independent validation relations](VALIDATION.md)
