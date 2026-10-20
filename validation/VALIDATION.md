# Decoder validation

This is a reusable decoder validation framework, not an ISO/IEC 15444-4
conformance claim or a publication approval system. It contains no official,
restricted, or standards-derived vectors.

## Running the checks

Use Python with the pinned `jsonschema` dependency in `requirements.txt`.
For example, from the repository root (installation is needed only once):

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r validation/requirements.txt
PYTHONPATH=validation .venv/bin/python -m unittest discover -s validation/tests -v
.venv/bin/python validation/run-validation.py generate --check
.venv/bin/python validation/run-validation.py verify
.venv/bin/python validation/run-validation.py inventory
.venv/bin/python validation/run-validation.py schemas
.venv/bin/python validation/run-validation.py all --no-external
```

`all` checks corpus reproducibility, schemas, technical inventory links,
generated decoder cases, independent numerical cases, and budgets. It builds the example harness with
`cargo build --example validation_decoder --locked`. It does not require
internal approvals, old results, or committed source snapshots. `--subject`
selects a different harness; `--no-build` uses the existing default binary.

All reports default to ignored `target/validation/`. The `run`, `budget`,
`official`, `numerical`, `htj2k`, `schemas`, and `all` commands accept `--output-dir`. Existing
tracked report paths are refused. Reports bind the Git commit, dirty flag,
current source and validation-tool hashes, and subject binary hash when run.
These describe the current execution, not the validity of historical evidence.
No command updates a committed source snapshot or creates an attestation.
The commands above leave tracked source unchanged.

CI initializes the crate's pinned Rust toolchain in a job-local `RUSTUP_HOME`
before building the native harness. This keeps validation independent of
preinstalled runner toolchain/component state.

## Reproducible corpus

`framework.py` deterministically generates 17 minimal raw codestream, JP2,
JPH, JPX, and JPIP fixtures, including negative, malformed-prefix, and
metamorphic cases. `corpus.json` retains byte lengths, hashes, recipes,
redistribution policy, expected outcomes, and metamorphic parents. `verify`
checks these bindings, path containment, identifiers, and unexpected files.
Intentional recipe changes can be regenerated with `generate` (without
`--check`); this maintenance operation updates the tracked corpus.

## Differential execution

The package-excluded example harness emits stable image/error observations.
Images normalize dimensions, component precision/sign, and integer samples;
errors normalize typed categories. Metamorphic cases compare normalized hashes.

`oracles.json` defines optional OpenJPEG, Grok, and JasPer command templates.
Use `--oracle-config` for another configuration. The framework neither downloads
nor bundles those programs. It checks `OPENJPEG_DECODER`, `GROK_DECODER`, and
`JASPER_DECODER`, then `PATH`. An absent unconfigured oracle is explicitly
`skipped`, not passed. An explicitly configured missing executable, crash,
timeout, or invalid output is a failure, not a skip or successful rejection.
External PGM/PPM images normalize to the same planar integer representation.

```sh
.venv/bin/python validation/run-validation.py run
.venv/bin/python validation/run-validation.py run --no-external --output-dir target/validation/local
```

`validation-results.json` records observations and oracle errors;
`disagreements.json` preserves acceptance/output differences. Stable
`oracle-disagreement-v1` IDs bind case, oracle, kind, and normalized hashes.
Unresolved differences make the run `blocked` (nonzero exit). An optional
external `--adjudication-file` can supply human decisions using
`oracle-adjudication.schema.json`; it is validated and never rewritten.
The generated `oracle-adjudications.json` is only a derived view. Without
external observations its status is `skipped`, not passed.

## Independent numerical regression checks

Install OpenJPEG's `opj_compress` and `opj_decompress` CLI tools (for example,
`libopenjp2-tools` on Debian/Ubuntu). The suite creates its own deterministic
nonzero 8/16-bit PGM/PPM images, including channel extrema. It encodes and decodes
them independently and compares the Rust decoder's sample planes.
It also exercises 256-by-256 grayscale/RGB images with multiple code-blocks.

```sh
.venv/bin/python validation/run-validation.py numerical
.venv/bin/python validation/run-validation.py numerical --output-dir target/validation/numerical
```

Cases cover grayscale/RGB, raw/JP2, tiles and nonzero origins, multiple quality
layers, progression orders, every legacy coding-style flag, SOP/EPH/PLT, and
reversible/irreversible transforms.
Lossless cases must reproduce the original and reference samples bit for bit.
Lossy cases record per-component maximum error, MSE, RMSE and PSNR, plus error
against the original image. PSNR is `null` when MSE is zero, rather than a
nonfinite JSON value.

These explicit **engineering regression budgets** compare against OpenJPEG;
they are not official Part 4 numerical tolerances:

| Irreversible case | Maximum sample error | Maximum per-component RMSE |
|---|---:|---:|
| 8-bit grayscale | 1 | 0.25 |
| 8-bit RGB | 2 | 0.5 |
| 16-bit grayscale | 8 | 2.0 |

`numerical-results.json` retains every failure and measured disagreement with
source, input, encoded-stream, output and executable hash bindings. Successful generated images and encoded files are temporary; recipes and
runner source are tracked. Failed inputs, encoded streams and reference images
are retained under the ignored output's `numerical-failures/` directory and
included in CI artifacts for reproduction and minimization.
Native execution has time, output and POSIX address-space/file-size bounds.
Reports include encoder/reference/subject timings and total case time. Each
native stage defaults to ten seconds; the aggregate case budget is three
times that timeout, including normalization. Output capture is limited to one
MiB and files to two MiB, with 512 MiB address space where available.
Missing default tools are explicitly `blocked`; configured missing tools,
process failures, invalid output and exceeded thresholds cannot pass.
`--encoder`, `--decoder`, `OPENJPEG_ENCODER` and `OPENJPEG_DECODER` select trusted
local tools. `all` includes this gate unless `--no-external` is selected.

### Independent HTJ2K checks

The separate `htj2k` gate uses OpenJPH's `ojph_compress` and `ojph_expand`.
Build the immutable revision listed in [REFERENCES.md](../REFERENCES.md)
with Git, CMake, and a C++ compiler available:

```sh
bash validation/build-openjph.sh
export OPENJPH_ENCODER="$PWD/target/validation/oracles/openjph-build/src/apps/ojph_compress/ojph_compress"
export OPENJPH_DECODER="$PWD/target/validation/oracles/openjph-build/src/apps/ojph_expand/ojph_expand"
.venv/bin/python validation/run-validation.py htj2k
```

The builder keeps the public reference checkout and build under ignored
`target/validation/oracles/`, disables SIMD for scalar reproducibility, and
rejects a modified or different-revision cached checkout. No upstream source
or binaries are included in the source package.

Generated nonzero cases exercise grayscale/RGB, 8/16-bit samples, sparse
coefficients, odd dimensions, tiles, nonzero origins, progression orders,
raw/JPH wrapping, and reversible/irreversible transforms. First-party fixed
codestream recipes cover positive/negative significance propagation and
magnitude refinement, combined refinement, and a minimum-value boundary.
Both the reference decoder and the subject must reproduce each fixed case's
known samples. Preencoded cases report `encoder_invoked=false`, empty encoder
options, and a `null` encoder timing; the encoder is not run for those cases.

For live lossless encoding, the reference's decoded samples must match the
original source before the subject runs. A reference self-roundtrip failure
is retained as a failure, not accepted as an alternative expected image.
The pinned reference encoder does not preserve the minimum-valued one-pixel
input with zero decompositions. Live encoder cases therefore use at least
one decomposition; an independently decoded fixed stream covers that
zero-decomposition boundary.

`htj2k-results.json` uses the same numerical schema, per-case engineering
thresholds, process bounds, hash bindings, and failure retention as the legacy
numerical gate. These comparisons do not establish official Part 4
conformance or exhaustive Part 15 coverage. Missing unconfigured tools block
the gate; an explicitly configured missing tool is an error.
`all` does not implicitly run `htj2k`; CI runs both commands explicitly.

## Nonzero selection relations

The Python regression suite also exercises the production `*_selected` APIs
on independently encoded nonzero images. It compares native full-resolution
and reduced-resolution output with OpenJPEG/OpenJPH, then compares region,
single-tile, rectangular tile-set, and tile-contained region output with exact
crops of the corresponding native full decode. Independent reference crops
must also meet the declared per-case numerical budgets.

```sh
PYTHONPATH=validation .venv/bin/python -m unittest discover \
  -s validation/tests -p test_selection.py -v
```

These tests cover raw, JP2, JPH, and JPX component decoding; grayscale/RGB;
8/16-bit samples; odd dimensions and nonzero origins; uniformly subsampled
components; and reversible/irreversible transforms. Reference resolution
reduction uses `opj_decompress -r` or `ojph_expand -skip_res`, not image
resizing. Nonzero fixtures additionally distinguish native DWT output from
simple post-decode decimation. Rectangles and reported output origins use the
image reference grid; PNM component dimensions are kept separate from the
subsampled image-grid extent.

Invalid nonrectangular tile sets and regions extending outside selected tiles
must retain typed selection errors. The tests do not relax those API
constraints. Tests needing unavailable native tools are explicitly skipped;
the CI setup installs both reference implementations before running them.
Disagreements retain source/encoded/reference files and a hash-bound
reproduction record under ignored `selection-failures/`, included in CI
artifacts. These component-selection tests do not replace JPX composition,
JPIP reconstruction, color-resampling, or official conformance checks.

The example harness exposes the same selection controls without changing its
ordinary full-decode path:

```sh
cargo run --example validation_decoder -- select raw image.j2k 1 all 4,6,32,24
cargo run --example validation_decoder -- select jp2 image.jp2 0 0,1 all
```

The arguments after the input are discard levels, `all` or comma-separated
tile indices, and `all` or `x,y,width,height`. Selected output begins with a
`FRAME` line containing the actual output origin, followed by the existing
image observation.

## Nonzero JPX and JPIP relations

The Python suite also builds first-party JPX and JPIP structures around
independently encoded nonzero samples:

```sh
PYTHONPATH=validation .venv/bin/python -m unittest discover \
  -s validation/tests -p test_container_relations.py -v
```

JPX relations cover 8-bit grayscale and 16-bit RGB layers, chroma-key
transparency, overlapping placements, source crops, frame persistence and
finite frame bounds. Expected canvases are calculated from the original
samples and authored placement rectangles, not from another subject decode.
These cases use opaque/binary alpha; they do not establish fractional or
premultiplied-alpha numerical conformance.

JPIP relations check byte-exact reconstruction from reordered, duplicated,
explicit/inherited-context fragments, followed by sample-exact legacy and
HT decoding. Independently decoded OpenJPEG quality prefixes provide expected
8/16-bit progressive images. Incomplete packets and repeated updates must not
emit new images; complete layers must advance monotonically and reproduce the
corresponding independent output. Stored legacy magnitude bits remain a
prefix while integer coefficient materialization adds the coefficient-local
truncation midpoint. The last fully decoded bitplane needs no integer offset.

Automatic progressive cases use the original packet-length metadata.
Explicit-plan cases use authored inline headers without obsolete PLT
declarations, and separately retain the rejection of unsupported headers;
tests do not broaden the manual API's supported profile.
No network transport or service is involved.

Failures retain generated inputs, reference images, tool hashes/options and
reproduction records under ignored `container-failures/`. Distinct input,
subject and test hashes select distinct failure directories, so a later
disagreement does not overwrite an earlier one. CI uploads those directories.

## Budgets

```sh
.venv/bin/python validation/run-validation.py budget
```

Defaults are five seconds per case, 30 seconds total, one-MiB input/output
caps, and 512 MiB address space where POSIX `RLIMIT_AS` is available. Execution
enforces bounded output capture and reports unavailable memory enforcement.
Decoder `ResourceLimits` remain active on every platform.

### Representative process measurements

On Linux, install GNU Time alongside the OpenJPEG tools and run:

```sh
.venv/bin/python validation/run-validation.py resources
```

This builds the release-mode harness and measures 1024-by-1024 grayscale and
512-by-512 RGB lossless inputs, each tiled at 128-by-128. Full decode, tile-zero
selection, and native resolution with two discarded levels must reproduce
independent OpenJPEG output exactly. Declared-pixel-limit and truncated-header
cases must produce their expected typed errors, not merely exit unsuccessfully.

Each of the eight cases is measured three times. GNU Time reports actual peak
process RSS; the bounded runner measures wall time including process startup
and image-observation serialization. The engineering thresholds are:

| Case | Maximum time per process | Maximum peak RSS |
|---|---:|---:|
| Full image | 5 seconds | 512 MiB |
| Tile/native-resolution selection | 2.5 seconds | 256 MiB |
| Early typed rejection | 1 second | 128 MiB |

Aggregate measured native time is limited to 30 seconds. Tile-zero peak RSS
must be at least 25 percent lower than full decode for each generated image.
Each process also has a one-GiB address-space limit and bounded output capture.
These measurements are not universal worst-case guarantees. Decoded sample
storage, address-space enforcement, and measured total-process RSS are distinct
quantities; the report keeps them separate.

`resource-results.json` retains source/tool/input/output hashes, repetitions,
individual observations, median times, peak RSS, thresholds and explicit
failures. Unavailable default tooling/platform support blocks the gate;
explicitly configured missing tools and absent measurements cannot pass.
Failed inputs are preserved under ignored `resource-failures/` and uploaded
by CI. `all` does not implicitly invoke this Linux-specific gate; CI calls it
separately. `--subject` selects a trusted prebuilt binary; `--no-build` uses
the existing release harness.

## Optional feature and performance comparison

The separate `compare-hayro` command pins hayro-jpeg2000 without changing the
production crate's dependencies. It qualifies common outputs against
independent references before reporting release-mode timings and peak RSS.
See [comparison methodology and feature evidence](COMPARISON.md) for exact
versions, output/lifecycle semantics, limitations and reproduction commands.
Default CI runs the capability/output checks; larger performance runs remain
explicit rather than noisy CI speed assertions.

## Technical reference inventory

`normative-coverage.json` is a static inventory of topics and implementation,
specification, executable contract, proof/view, and test references. Its
validator checks every present item, including contracts that ensure a listed
spec and are called by the claimed implementation. Shadow-only links fail.
It does not assert exhaustive standards-clause coverage, exact progress
counts, phase completion, or conformance.

## External official vectors

Assets remain in an authorized, externally managed directory and are never
copied into the repository or report artifacts. Use `--vector-root` or
`JPEG2000_OFFICIAL_VECTOR_ROOT`, and `--manifest` or
`JPEG2000_OFFICIAL_VECTOR_MANIFEST`. The default external manifest name is
`official-vector-manifest.json`.

The manifest schema requires source/acquisition metadata, authorized-use and
license evidence, redistribution disabled, archive and input byte/hash
bindings, explicit selection, and independently established normalized hashes
for accepted cases. Paths are confined to the external root. A manifest's
source URL identifies its suite; no private standards-profile file is needed.
These declarations must reflect the operator's actual rights and evidence.

```sh
JPEG2000_OFFICIAL_VECTOR_ROOT=/authorized/vector-root \
  .venv/bin/python validation/run-validation.py official
```

Missing access/configuration produces an explicit `blocked` report and nonzero
exit. Invalid manifests fail before execution. Reports contain hashes,
permitted public identifiers, counts, timing, normalized hashes, and geometry,
not private paths, identifiers, samples, or asset bytes. Archive-integrity,
execution, and resource failures cannot pass. This optional command is not
part of clean-clone `all`.

## Proof report

After an actual pinned whole-crate Verus run:

```sh
.venv/bin/python validation/generate-proof-coverage.py target/validation/verus-result.json
.venv/bin/python validation/run-validation.py schemas
```

The default report is `target/validation/proof-coverage.json`; `--output-dir`
selects another directory. The checker requires the pinned commit,
whole-crate success, zero errors, nonempty project results, and no unmapped
termination bypasses or trusted proof escapes. It does not compare against
committed progress output or infer coverage for absent functions. CI retains
the stable release's `--no-lifetime` boundary explicitly; lifetime verification
is not claimed.
