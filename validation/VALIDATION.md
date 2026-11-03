# Decoder validation

This is a reusable decoder validation framework, not an ISO/IEC 15444-4
conformance claim or a publication approval system. It contains no official,
restricted, or standards-derived vectors.

## Running the checks

### Review-policy administration audit

Technical CI and manual solo-owner review are separate responsibilities.
The [review policy](../PROOFS.md#solo-owner-review-and-technical-ci) replaces
the historical per-file-combination hold only after a separately authorized,
owner-reviewed live configuration migration. No CODEOWNERS roster is
fabricated. Normative adjudication and release permissions remain separate.

An operator can capture main ruleset25421374 with the read-only GitHub API and
run `python3 validation/review_policy.py path/to/fresh-ruleset.json`.
This checks the solo-compatible review settings and all twelve technical check
names/app identities. It never writes settings or approves a PR, and cannot
prove that a supplied snapshot is live or that a reviewer is qualified.
It reports that owner-comment review is manual, not independently enforced.
Before/after API receipts and actual current-commit owner-decision/check evidence
remain necessary. The current pre-migration configuration must fail this audit.

### Dependency-update proposals

Dependabot checks Cargo at the repository root and `fuzz/`, validation's
hash-locked pip inputs and GitHub Actions weekly. It groups ordinary version
updates and limits them to one open version-update PR per ecosystem; this is
not a blanket limit on security updates. It does not merge or publish anything.
Verifier dependencies `vstd` and `verus_*` are excluded from automatic update
proposals. Actual pin/resource/trust changes still require explicit owner review.

The `.github/dependabot.yml` file uses JSON syntax, a valid YAML subset, so
standard-library tests can validate the exact configuration without adding a
YAML-parser dependency. The image-consumer probe deliberately depends on the
generated unpacked package under `target/package/`, not the live source crate.
It is not a standalone Dependabot Cargo root. Update its pinned `image`
dependency manually and run the existing package/consumer/MSRV gates; never
redirect that path merely to make dependency automation succeed.

CI and Verus already have unfiltered `pull_request` triggers, including PRs
targeting `release/0.1`; no new release-branch workflow or publisher is needed.
Push validation and release promotions remain subject to the existing branch
workflow and explicit freeze authorization. No frozen release ref is modified
by dependency configuration. Optional preflight is not a release publisher.

### Decoder and framework commands

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

The harness formats integer samples directly into one comma-separated row
buffer, avoiding a separate allocation for every sample. Signed, unsigned
and converted output bytes are unchanged and checked by harness regressions
and independent numerical comparisons. This reduces validation-subject
serialization overhead; it is not a decoder throughput or conformance claim.

Inventory validation reuses content-keyed implementation ranges and file
call-name indexes within each invocation. A fresh invocation rereads its
source files and rebuilds the indexes, including after source mutations.
Owner/trait selection, duplicate-method rejection and same-file executable
body checks are unchanged. Cross-file matching retains the previous
conservative word/token rules; it is not a Rust parser. These indexes avoid
repeated full-source regex scans without selecting fewer tests or relaxing
contract, source-linkage or mutation-rejection checks.

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

### Native numerical platform gates

The separate native numerical matrix builds the same pinned OpenJPEG and
scalar OpenJPH source revisions on Ubuntu, macOS and Windows, then runs the
legacy/HT numerical commands and numerical/selection/container regressions
using each platform's native executables. This is independent numerical
execution, not an inference from portable Rust unit tests. Reports are retained
in platform-named artifacts, with source/tool/executable hashes and explicit
execution-platform and requested-limit metadata.

```sh
bash validation/build-openjpeg.sh
bash validation/build-openjph.sh
```

The builders require Git, CMake and a C/C++ toolchain, select Release for both
single- and multi-configuration generators, and reject modified/wrong-revision
source checkouts. OpenJPEG is pinned at
`a5891555eb49ed7cc26b2901ea680acda136d811` (2.5.0); OpenJPH retains its existing
0.33.0 pin. The OpenJPEG build enables the required PNM/PGX/RAW paths without
optional PNG/TIFF/ICC-engine libraries. Windows generators may place OpenJPH `.exe` files in a `Release`
subdirectory; CI requires exactly one matching executable before exporting
its configured tool path.

Windows capture uses bounded pipe-reader queues rather than POSIX pipe
selection. Timeout, combined stdout/stderr capture bounds and nonzero exit
status remain explicit; POSIX setup callbacks cannot be silently discarded.
Address-space limits are requested on Linux only; macOS rejects that setup.
File-size limits are requested where the POSIX resource API is available.
Unavailable limits are reported as `null`, including both on Windows.
These numerical checks do not claim identical
OS enforcement or measured memory guarantees: the separate GNU Time/RSS
resource gate remains Linux-only.

Per-component quantization snapshots use bounded heap storage sized to the
actual component count, avoiding large fixed-array copies on the default
Windows main-thread stack. `ComponentQuantizations` is `Clone`, not `Copy`;
borrow it for reads or explicitly clone an owned snapshot. A one-MiB-stack
decoder regression checks this on Linux, while Windows numerical execution
uses the native default stack rather than a larger configured stack.

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
nonzero 8/16-bit PGM/PPM images, including channel extrema, plus monochrome PGX
inputs retaining signedness and non-byte-aligned precision. It encodes and
decodes them independently and checks the Rust decoder's typed sample planes.
It also exercises 256-by-256 grayscale/RGB images with multiple code-blocks.

```sh
.venv/bin/python validation/run-validation.py numerical
.venv/bin/python validation/run-validation.py numerical --output-dir target/validation/numerical
```

Cases cover grayscale/RGB, raw/JP2, tiles and nonzero origins, multiple quality
layers, progression orders, every legacy coding-style flag, SOP/EPH/PLT, and
reversible/irreversible transforms.
PGX observations add signed 1/2/4/7/8/9/12/16/17/24-bit and unsigned
1/2/4/7/12/20/24-bit samples,
including signed JP2, odd geometry, tiled nonzero origins, vertical causality,
and layered raw-bypass coding. PGX storage uses one byte through 8 bits, two
through 16 bits, and four through 32 bits; nominal precision and signedness
remain separate metadata and are checked exactly. Both PGX byte orders,
payload lengths, declared ranges and the decoder's indexed component filenames
are validated.
For the selected sub-8-bit cases, PGX remains the original/reference format,
but the encoder receives unsigned RAW sample bytes with explicit precision
through `-F`. The pinned PGX/PNM input converters promote those inputs to
8 bits, so their direct output is not substituted for the intended low-bit
image. RAW inputs preserve the actual sample words and SIZ precision.
Reports identify `encoder_input_format`, actual input hashes and encoder
options, separately from the original source format.
Signed fixtures encode the offset unsigned source, whose centered transform
coefficients are identical, then author the signed SIZ flag and matching JP2
bit-depth flag. This avoids PGX input converters that recompute precision from
positive samples and discard the sign bit. Reports explicitly distinguish the
original signed source from the actual unsigned encoder input and identify
authored headers. No coefficient or packet-body bytes are changed. The
independent decoder must still reproduce the original signed metadata and
samples exactly; a rewritten header alone cannot qualify a fixture.
Selected signed/unsigned 25-bit profiles qualify at zero DWT decomposition,
including layered raw-bypass, odd tiled geometry and signed JP2.
Selected RGB16 reversible cases cover enabled and disabled component
transforms at two decompositions. A separate RGB16 irreversible case retains
fixed ceilings of 8 samples maximum error and 2.0 worst-component RMSE.
Main-header
segments are traversed by their lengths, including inside JP2 wrappers.
The actual COD decomposition level must match the case; declared quality-layer
and coding-style options are also checked against COD. Marker-like bytes
inside comments do not satisfy required RGN/NLT checks.
Lossless cases must reproduce the original and reference samples bit for bit.
The generated stream must first independently decode to the original geometry,
precision, signedness and samples; a changed reference is a failure, not a new
expected image. PGX origin cases use equal nonzero offsets; asymmetric origins
remain covered by the PNM cases. The legacy generated matrix does not qualify
25-bit DWT transforms, precisions above 25, every intermediate precision/style,
or multicomponent precision above 16 bits. Wider full-range probes that failed
the independent original/reference roundtrip were not adopted as expected
outputs or successful cases.
The layered bypass case also covers a zero-byte contribution completing a
buffered MQ segment. Such a continuation must retain and replay its bounded
prefix; it does not make an empty initial legacy segment valid.
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

### Nonuniform component grids and selected color

Container relation tests generate their own planar 8/16-bit 4:2:0 and 4:2:2
sources, including nonzero origins and odd tile boundaries. Independent
component-selective PGX decoding must reproduce every original plane exactly
before the subject runs. Native discard levels are separately checked against
independent component decoding, not simple sample decimation.

sRGB resampling is checked exactly, with independent component upsampling at
aligned origins. Aligned-origin sYCC output has explicit engineering maximum
errors of 2 samples at 8 bits and 12 at 16 bits after common-depth normalization:
the reference converter uses rounded matrix coefficients and integer
truncation. These are not official color-conformance tolerances. Odd-origin
edge filling is checked against the decoder's documented clamping policy, not
claimed equivalent to the reference's different boundary policy.

Full and region/tile/tile-set color outputs must agree exactly after cropping
at the same native DWT resolution, including one-pixel and chroma-unaligned
regions. Half-grid CRG fixtures separately exercise registration phase.
The tests cover JP2/JPX and authored HTDECLARED all-legacy JPH wrappers with
unchanged independently qualified legacy coefficient/packet bytes; they do not
claim independent nonuniform HT encoding. The existing live HT suite remains
separate.

Color-selected paths retain required sampling context before conversion and
crop afterward. Invalid original selections are still rejected before context
expansion, and ordinary resource limits cover any additional decoded context.
An empty-resolution precinct consumes its packet header even when its present
flag is set and it contains no code blocks. Input/tool/source hashes and failing
fixtures are retained under the existing `container-failures/` artifacts.

### Broader selected color, opacity, ROI, quality and mixed profiles

A finite twenty-candidate generated-profile qualification was declared and
hashed before native measurements. All original/reference dispositions were
persisted before subject measurements: fourteen references qualified and
fourteen subject profiles passed; six candidates remained reference-unqualified
or explicitly excluded.
No thresholds were changed to admit a candidate. These are engineering
observations, not official Part 4 evidence or a normative certificate.

Four additional 47x35, 16x16-tiled, two-decomposition numerical cases retain
the original 56 legacy/48 HT cases and budgets:

| Profile | Origin | Original/reference and reference/subject budget |
|---|---|---|
| `q2-roi-gray20`, component 0 upshift 1 | (3,3) | exact |
| `q2-roi-rgb16-independent`, component 2 upshift 2, MCT disabled | (3,5) | exact |
| `q2-roi-gray16-irreversible`, component 0 upshift 2 | (3,5) | maximum error 8, worst-component RMSE 2.0 |
| `q2-quality-rgb16-layered`, layers `8,3,1`, coding style 63, MCT enabled | (3,5) | exact |

Both comparisons must meet the irreversible budget, before/after the subject
respectively. PGX uses equal x/y origin because the pinned PGX encoder's
asymmetric-offset handling changes the requested geometry; actual SIZ/COD
must still match. This does not qualify the rejected asymmetric PGX path.
`selection.py` obtains every native reference at discard 0/1/2 before testing
full, region, single tile, tile-contained region and rectangular tile-set
selections. Its expected crops come exclusively from independent native
planes, with absolute-grid ceilings and exact origin checks.
The layered RGB16 case also covers zero-byte later terminated MQ/RAW passes
and raw ERTERM tails in a complete independently encoded image. Its earlier
`InvalidCodeBlock` disagreement is resolved by the corrected shared Tier-1
reader/pass termination behavior, not by changing the input or expectations.
Full decoding and every selection at discard 0/1/2 must remain exact; final
quality-layer success alone does not qualify arbitrary quality-prefix output.

`container_relations.py` uses `fractions.Fraction` for independent sample
normalization and source-over, not a call into Rust color/composition code.
Four nonuniform 32x32 color profiles cover 8/16-bit sRGB at odd origin (1,3)
and sYCC at aligned origin (2,4), 4:2:0 or 4:2:2 sampling, 16x16 tiles and
native discard 0/1/2. Independently decoded component PGX planes must first
reproduce the originals exactly. Nearest-component sampling retains the
absolute native-grid phase. sRGB requires exact normalized-16 output.
sYCC uses rational coefficients 1.402, 0.344136, 0.714136 and 1.772, clipping
in the original sample range before normalization, with frozen normalized-16
maximum-error and worst-component-RMSE ceilings of 514 at 8 bits and 12 at
16 bits. These intentionally fixed engineering ceilings are not official
colorimetric tolerances.

Four gray/global-alpha profiles add unsigned 8/16-bit straight/premultiplied
samples with alpha physically first, fractional/boundary alpha, nonzero
origin (3,5), and JP2/indexed-JPX/HTDECLARED all-legacy JPH wrappers.
Full and selected conversion is exact against independently decoded planes;
straight-alpha cases additionally use discard 1/2. Premultiplied cases are
deliberately zero-DWT/full-resolution: general wavelet-domain preservation
of the color-not-exceeding-alpha constraint is not presumed. JPX static/frame
composition, cropped/scaled placement and overlap require exact rational
source-over, rounding each placement to the nearest output sample. Gray plus
alpha retains two channels; it is not silently relabeled RGBA.

Two nonzero mixed legacy/HT profiles author a 64x32 two-tile codestream from
independently qualified 32x32 legacy/OpenJPH tiles. The main CAP explicitly
declares HTDECLARED and heterogeneous tile headers; the legacy tile carries
its own COD/QCD. Constituent roundtrips alone are insufficient: unmodified
OpenJPEG must decode the **complete mixed stream** exactly to the original
two-tile image before any subject comparison. Its native reduced output is
also the reference for full/region/both single tiles/tile-contained selections
at discard 0/1/2 in raw and JPH. OpenJPH's rejection of legacy tile headers is
retained in qualification evidence, not patched or counted as another pass.
This is selected mixed-tile evidence, not arbitrary in-code-block HT/MQ
switching or every mixed-profile capability combination.

The six nonpassing candidates remain explicit boundaries:

| Candidate | Disposition |
|---|---|
| Signed12 Maxshift `U=2`, layers `8,3,1`, bypass, tiled DWT2 | original/reference maximum error 752 exceeds exactness |
| RGB8 irreversible layers `8,3,1`, tiled DWT2 | original/reference maximum error 3/RMSE 0.6991 exceeds frozen 2/0.5 |
| Gray8 and gray16, 32x32, zero-DWT `8,3,1` quality prefixes | first independent prefix is constant; no meaningful three-prefix qualification |
| Native JPX compositor | neither pinned CLI exposes independent layer/frame rendering; rational generated profiles are a narrower substitute, not native semantic equivalence |
| ICC execution | deliberately not implemented; pinned reference build has ICC execution disabled |

None of these six has been turned into an expected-rejection “passing
numerical case” or erased from the denominator. Existing quality-prefix
regressions remain; the qualified final-layer RGB16 addition does not add a
qualified new three-prefix profile.

The existing three-platform native regression invocation runs the new
numerical, selection and container tests without platform-specific thresholds:

```sh
PYTHONPATH=validation python -m unittest -v \
  validation.tests.test_numerical \
  validation.tests.test_selection \
  validation.tests.test_container_relations
```

All four native executable directories must be on `PATH` (or the supported
OpenJPH environment paths) so optional native tests actually execute.
New supplemental matrices, reference snapshots (written before subjects),
sample/input/tool hashes, commands and subject observations are retained in
ignored `target/validation/q2-selection/`, `q2-container/` and `q2-mixed/`.
The numerical command continues to use the existing numerical report schema.
The supplemental JSON is regression evidence, not a new normative report
schema. Local execution does not satisfy exact-head three-OS or final-main
integration gates, and neither case count nor these fourteen profiles closes
the remaining broader qualification gaps.

### Component Maxshift and binary-complement NLT

Additional legacy cases exercise component-wide `RGN` upshifts for grayscale,
16-bit data, different RGB component indices, JP2, nonzero tiled origins,
quality layers and selected signed data. The requested RGN component/style/
shift header must actually be present. This CLI mechanism upshifts a whole
component; it is not evidence for arbitrary spatial ROI masks. Native
resolution, region, tile and tile-set relations are checked separately.

Live OpenJPH cases encode finite signed binary32 patterns with NLT type 3 at
zero, one and two DWT decompositions, including a signed JPH container. The
required NLT header must be present; signed-header authoring is not substituted
for this live transform. The independent PFM output and the subject's typed
32-bit signed words must preserve every original bit, including distinct
positive and negative zero. Reports label the representation
`ieee754-binary32-bits`; integer-word error metrics here are bit-exactness
diagnostics, not floating-point intensity or PSNR claims.

The PFM helper reads words in stored scanline order and only supports unit
scale and binary32 fixture payloads. Repeated rows isolate the nonlinear
sample transform; this is not general PFM orientation, NaN/infinity, color
management, other NLT-type or full floating-point codec qualification.
Failures still retain original/encoded/reference inputs and source/tool hashes.

HT cleanup U/MagSgn precision includes the sign-coding bit in addition to the
coefficient magnitude bound. The paired implementation/specification and
boundary regressions keep these limits distinct: up to 74 coefficient
magnitude bits and 75 MagSgn bits, with out-of-range values still rejected.
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

Selected RGB16 cases additionally cover sparse and multi-code-block images,
odd tiled nonzero origins, JPH wrapping, and both enabled component transforms
and independently coded components. An explicit `-colour_trans` setting must
agree with the actual COD field. Lossless cases require exact original,
reference and subject planes. The irreversible RGB16 case uses a fixed
engineering ceiling of 8 samples maximum error and 2.0 worst-component RMSE
against the independent output; these are not official conformance tolerances.
Region/tile/tile-set/native-resolution tests separately exercise both lossless
transform modes at asymmetric nonzero tiled origins, including JPH.

Selected signed and unsigned monochrome 25-, 26-, 28- and 31-bit HT cases
additionally cover full-range samples at two reversible decompositions.
Canonical PGX sources and native little-endian RAW encoder inputs have
separate hashes and signedness provenance; the RAW path is not described as
authored signed metadata. Actual SIZ geometry, component precision/sign and
sampling, and COD decomposition/wavelet/component-transform fields must match
the declared case. This does not qualify full-range zero-DWT encoding at those
precisions or multicomponent precision above 16 bits; unsuccessful
original/reference probes are not installed as passing or skipped cases.

For live lossless encoding, the reference's decoded samples must match the
original source before the subject runs. A reference self-roundtrip failure
is retained as a failure, not accepted as an alternative expected image.
The pinned reference encoder does not preserve the minimum-valued one-pixel
input with zero decompositions. Live cases for that ordinary unsigned
minimum-valued profile therefore use at least one decomposition; an
independently decoded fixed stream covers its zero-decomposition boundary.
Separately qualified binary32 NLT cases include live zero-DWT encoding.

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
The original cases retain opaque/binary alpha and their separate strict oracle.
Additional RGBA fixtures independently encode/decode every 8/16-bit color and
opacity plane before authoring CDEF channel roles or JPX OPCT declarations.
They cover fractional alpha including near-zero/near-opaque endpoints,
straight/premultiplied representation, reordered channels, 2-by-2 alpha
subsampling, and explicit opacity overrides.

A separate oracle uses Python `Fraction` arithmetic for source-over in
normalized sample space, rounding each output color/alpha to 16 bits after
each layer. It does not copy the production integer expression or consume
subject outputs as expectations. Static composition, placed/scaled/clipped
crops, persistent/nonpersistent frames, and equivalent straight/premultiplied
encodings must match exactly. Invalid premultiplied samples are rejected by
composition. Single-layer rendering preserves its samples and alpha
representation flag rather than pretending premultiplied samples are straight;
composited transparent pixels are transparent black.

This qualifies selected whole-image/global-alpha sRGB fixtures, not all
per-color/multiple-opacity associations, higher precision, linear-light
colorimetric blending, a third-party JPX compositor, or official alpha
conformance. Authored container metadata and the independently qualified
coefficient payloads remain distinct evidence. Nested fixture files, tools,
test sources and subject hashes are included in retained failure records.

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

On Linux, install GNU Time alongside the OpenJPEG tools, build the pinned
scalar OpenJPH tools as above, and run:

```sh
.venv/bin/python validation/run-validation.py resources
```

This builds the release-mode harness and measures 1024-by-1024 grayscale and
512-by-512 legacy RGB8/RGB16 and HT RGB16 lossless inputs, each tiled at 128-by-128. Full decode, tile-zero
selection, and native resolution with two discarded levels must reproduce
independent reference output exactly. Declared-pixel-limit and truncated-header
cases must produce their expected typed errors, not merely exit unsuccessfully.
HT cases require exact original/OpenJPH agreement and actual SIZ/CAP/COD
geometry and HT coding signals. Their tile-zero expectation is a checked crop
of the full independent lossless decode; native reduction uses independent
`-skip_res` synthesis, not decimation. The shared crop helper also serves the
selection tests and rejects inconsistent frame/component geometry.

### R1 finite workload declaration (before measurement)

#### R1 bounded accounting-frontier stage (frozen before measurement)

The following separate matrix extends, rather than replaces, the existing
45-case gate. It declares four small fixture families and five actual harness
paths, with both `DecodedBytes` and `WorkUnits` admission-budget tasks for each
path. Each task observes zero rejection, an independently qualified accepted
ceiling, at most 32 binary-search probes, and an observed accepted frontier
and adjacent typed rejection, each then repeated three times. Thus the stage
adds exactly 20 final cases / 60 final observations and at most 320 probes.
All observations, including the unchanged baseline 45 cases and its probes,
share the original 30-second aggregate wall gate. No per-case, rejection,
selection, RSS, child-address-space, file or capture cap is relaxed. New
rejection probes additionally obey the 1-second / 128-MiB rejection cap.
If qualification, a ceiling, a frontier or the aggregate gate fails, the stage
is failed/incomplete; no path is dropped or ceiling/cap tuned after measuring.

This JSON is the canonical matrix: hash its UTF-8 canonical JSON (sorted keys,
compact separators, followed by one newline). The report retains that hash.

```json
{
  "id": "r1-effective-frontiers-v2",
  "baseline_cases": 45,
  "paths": [
    {"id": "selected-raw", "family": "selected", "operation": "select", "format": "raw", "size": 32, "components": 1, "precision": 8, "tile_size": 16, "decomposition_levels": 2, "output_protocol": "selected-image", "output_components": 1},
    {"id": "selected-color", "family": "selected-color", "operation": "select-color", "format": "jp2", "size": 32, "components": 3, "precision": 16, "tile_size": 16, "decomposition_levels": 2, "output_protocol": "image", "output_components": 3},
    {"id": "jpx-compose", "family": "composition", "operation": "render", "format": "jpx", "size": 16, "components": 3, "precision": 16, "tile_size": 16, "decomposition_levels": 2, "output_protocol": "image", "composited_layers": 2, "output_components": 4},
    {"id": "jpip-reconstruct", "family": "jpip", "operation": "reconstruct", "format": "jpip", "size": 16, "components": 3, "precision": 16, "tile_size": 16, "decomposition_levels": 2, "output_protocol": "reconstructed-image", "output_components": 3},
    {"id": "jpip-progressive", "family": "jpip", "operation": "progressive", "format": "auto", "size": 16, "components": 1, "precision": 8, "tile_size": 16, "decomposition_levels": 0, "output_protocol": "progressive", "expected_updates": 7, "output_components": 1}
  ],
  "ceilings": {"DecodedBytes": 1048576, "WorkUnits": 100000},
  "maximum_search_probes": 32
}
```

Revision v1 (matrix hash
`f26c3dfe59b6605045a1dd62e12c7863843c9e54a6b7d0c4365c995d8736e993`)
is retained as a failed/incomplete stage: its selected-color oracle incorrectly
invented an opaque alpha channel for RGB JP2 conversion. `convert` constructs
only declared color/alpha channels; composition separately supplies implicit
opacity. Revision v2 freezes the corrected three-channel RGB source
expectation and makes all expected output cardinalities explicit before
remeasurement. No fixture input, path, sample-value budget, search ceiling,
process cap or baseline case was changed; composition still tests RGBA16.

Selected paths use discard zero / tile zero and exact checked crops of the
original/reference full decode. Selected color uses authored sRGB JP2 metadata
and the exact RGB16 source crop (no undeclared alpha channel). Composition uses
two independently losslessly qualified full-canvas opaque RGB16 layers; the
foreground source plus opaque alpha is the expected canvas. Reconstruction
uses the existing split/reordered/duplicated main/tile/body databins and must
reproduce both encoded bytes and decoded samples exactly. Progression uses a
separate zero-DWT, single-layer lossless grayscale stream with checked PLT
single-packet signaling and three complete main/tile/precinct databins.
It must report seven updates, exactly one independently qualified image, and
final complete layer one; partial error prefixes remain observed, not invented
from expectations. No multi-quality-layer progression claim is made here.

The harness only tightens one existing hardened default through the existing
checked limit builder and passes those options into the real selected,
conversion, composition, cache/reconstruction and progressive APIs. These
are **effective admission-budget frontiers / maximum prefix claims for these
exact paths**, not global cumulative work across counter-reset scopes, total
allocations, process RSS, CPU time, or universal minimum budgets. Expected
sample storage remains separate. This matrix does not cover arbitrary
selections, HT accounting, all container/color/opacity combinations, multiple
progressive quality layers, sustained R2 campaigns or default-maximum stress.
Passing it is not whole-R1 completion or integration into actual main.

The original 22 cases, 66 final measurements, four finite budget searches,
and all existing caps remain mandatory. The following additional Linux
production-default workloads are declared before collecting R1 measurements.
All positive streams are reversible, use two decomposition levels and require
exact original/reference qualification before any subject observation. These
are safe representatives, not allocations at the production maxima.

| ID/family | Declared workload | Subject observations |
|---|---|---|
| `large-gray` | 1536x1536 unsigned8, 128x128 tiles | full, tile zero, native discard 2 |
| `components8` | 128x128, eight unsigned16 planes, no MCT | full |
| `precision24` | 256x256 unsigned24 PGX | full |
| `tiles256` | 512x512 unsigned8, 32x32 tiles (256 tiles) | full, tile zero, native discard 2 |
| `layers16` | 128x128 RGB16, 16 quality layers, final lossless layer | full |
| `ht-large` | 768x768 RGB16, 128x128 HT tiles | full, tile zero, native discard 2 |
| `jpx-components` | 256x256 RGB16 payload in authored JPX metadata | codestream decode |
| `jpx-compose` | two independently qualified 128x128 RGB16 opaque layers | two-layer composition, exact RGBA16 source oracle |
| `jpip-fragments` | 256x256 RGB16 single tile; three databins, split/reordered/duplicated fragments | reconstruction bytes and exact decoded image |
| `jpip-ht-fragments` | same geometry and fragmentation, true HT payload | reconstruction bytes and exact decoded image |
| `declared-*` | tiny declarations exceeding default width, height, component, tile, layer, JPX-codestream or JPIP-fragment-offset limits | exact typed early rejections |

The implementation adds 16 positive observations and seven early rejections
to the 22-case baseline: 45 cases and 135 final measurements, in addition to
the unchanged four bounded searches (104 probes for these baseline fixtures).
Every final observation is repeated three times. Existing full/selection/
rejection wall/RSS caps, selection/full RSS ratio <=0.75, child address space
<=1 GiB, file <=32 MiB, captured output <=16 MiB and aggregate native wall
<=30 seconds are unchanged. CPU user/system seconds are measured separately
with GNU Time; work units are not CPU time. Positive output must fit capture
without truncation. Unsupported reference formats and original/reference
disagreements remain unqualified failures, never substituted expectations.
No giant maximum-sized stream, unbounded stress, fuzz-limit replacement or
cap tuning is authorized by this matrix.

The raw parser retains per-tile component-style cache indices into the latest
same-tile payload owners instead of duplicating their dense style arrays.
Bounds, same-tile ownership, latest-owner selection and absence are maintained
inductively from the real parser updates. This does not skip unselected headers,
discard unused style fields or change inheritance, error order or resource
charging. Native RSS and instrumented allocation profiles remain distinct;
reduced cache storage is not a universal process-memory guarantee.

The eight-component case uses independently encoded planar unsigned16 raw
samples (`-mct 0`), with each original plane compared exactly against an
independent PGX decode. Other positive payloads likewise require exact
original/reference agreement and checked SIZ/COD geometry, precision,
component count, tiling and layer count; HT additionally requires CAP/style
signaling. JPX metadata is first-party authored, not third-party composition
evidence. Its opaque full-canvas foreground expectation is calculated from
the qualified source samples with an explicit RGBA16 alpha plane. JPIP checks
both the reconstructed codestream hash and decoded sample hash, with no
replacement by subject-derived expectations. A reference disagreement is
retained as an unqualified failure with source/encoded/reference artifacts.

The baseline retains four codestream-decoding budget frontiers. The bounded
accounting stage adds ten effective path frontiers through test-harness-only
`select-limited`, `select-color-limited`, `render-limited`,
`reconstruct-limited` and `progressive-limited` operations. The harness also
supports limited conversion/layer/frame modes, but these are not additional
qualified accounting paths. Append the ordinary selection arguments first,
then `decoded-bytes|work-units` and the checked numeric limit; legacy
`decode-limited` and ordinary invocations keep their interfaces. Unsupported
limited operations, selectors, malformed limits and attempts to raise
hardened defaults fail as usage errors before reading the input.
No global counter or alternative codec was added. Global cumulative byte/work
instrumentation across reset scopes, broader profiles and amplification
attribution remain open; default-maximum allocation and sustained R2 stress
are not authorized by this stage. Passing these finite matrices alone does
not close R1 or establish a universal resource envelope.

`--ht-encoder` and `--ht-decoder`, or `OPENJPH_ENCODER` and
`OPENJPH_DECODER`, select trusted HT tools. Missing unconfigured tools block
the full gate; an explicitly configured missing tool is an error. Legacy and
HT reference executable hashes are recorded separately.

The gate also independently qualifies 32-by-32 unsigned24 grayscale and RGB16
fixtures. The latter has three quality layers, 16-by-16 tiles and an asymmetric
origin; the required SIZ/COD fields are checked, not inferred from encoder flags.
For each fixture, a bounded search finds an observed adjacent decoded-byte
success/rejection pair and an observed adjacent work-unit pair. The test-only
`decode-limited` operation tightens exactly one `ResourceLimits` value; other
limits retain their hardened defaults. The search first requires typed rejection
at zero and exact independently decoded output at its ceiling (16 MiB decoded
bytes or 10,000,000 work units). It uses at most 32 probes per fixture/resource.
Each accepted frontier and the budget one unit below it are then rerun three
times. The lower budget must report the exact configured resource/limit and an
excessive claim; process failure or a different typed error cannot qualify.

Each of the forty-five baseline and twenty accounting final cases is measured
three times. Every search probe
also retains its budget, wall time, peak RSS, return code and exact output hash
or typed limit claim. GNU Time reports actual peak
instrumented-subject process RSS and user/system CPU time (seconds converted
to milliseconds, with the tool's native 0.01-second CPU granularity, so short
calls can report zero CPU). The bounded runner measures wall time including process startup
and image-observation serialization. The engineering thresholds are:

| Case | Maximum time per process | Maximum peak RSS |
|---|---:|---:|
| Full image | 5 seconds | 512 MiB |
| Tile/native-resolution selection | 2.5 seconds | 256 MiB |
| Early typed rejection | 1 second | 128 MiB |

Aggregate measured native wall time, including search probes, is limited to 30 seconds.
User CPU, system CPU and their sum are aggregated separately, not inferred from
wall time or work units. These aggregates exclude reference fixture generation
and the Python driver's image comparison; peak RSS is not a sum over the
driver/reference/subject process tree.
Search probes obey the same per-process thresholds as their accepted-frontier
case. Tile-zero peak RSS
must be at least 25 percent lower than full decode for each generated image.
Each process also has a one-GiB address-space limit and bounded output capture.
These measurements are not universal worst-case guarantees. Decoded sample
storage, address-space enforcement, and measured total-process RSS are distinct
quantities; the report keeps them separate.
An observed adjacent budget pair is not a theorem that all lower values fail
for every decoder path, nor a universal minimum budget. A decoded-byte limit
controls accounted decoder claims, not total process RSS. Work units are an
implementation accounting threshold, not a CPU-time or instruction count.
These finite fixtures do not characterize all production-default or worst-case
inputs, every high-component/precision/HT/container combination or every supported platform.

Resource report schema version 5 records the declared matrices, original/reference
qualification hashes (including source/reference files), CPU measurements,
default typed declaration claims, exact JPIP reconstructed-byte hashes,
configured budgets, finite search evidence and repeated frontier observations.
The runner rejects omitted/duplicate cases, changed declarations, mismatched
hashes/CPU aggregates and absent adjacent search observations. Schema checks
also fix the original wall/RSS/aggregate/process caps rather than accepting
report-specific relaxed values.
Every nonzero final measurement or search probe retains its actual parsed
typed category, reason and diagnostic in `observed_error`, independently of
the row's expected metadata. Every actual `LimitExceeded` observation also
retains its parsed resource/limit/actual claim, even when no limit was
configured. The unchanged baseline `declared-pixel-limit` fixture declares
65535-by-65535 pixels against the production default of 100,000,000 pixels;
each observation must report `Pixels`, limit 100,000,000 and actual
4,294,836,225. The truncated-header case retains its actual
`MalformedInput/Truncated` diagnostic. Missing observations are not inferred
from expectations or backfilled into earlier reports; category/reason/claim
disagreements fail validation.
The baseline `records` array still has exactly 45 cases; the separate
`accounting_records` array has 20 cases. Both arrays' final and search runs
contribute to the same CPU/wall aggregates. The resource CLI's ordinary
`cases` summary remains the baseline count; inspect `accounting_records` for
the additional stage. The report binds the frozen accounting matrix hash,
actual limited commands, output protocols and independent expectations.
Progressive observations additionally retain actual update metadata and the
captured protocol hash, including valid update prefixes before typed errors.
`typed_sample_bytes` uses the existing canonical eight-byte-per-integer-sample
convention, not physical converted-u16 buffer size or accounted decoder
claims. Accounting rejection rows retain the independent expected output
metadata so any emitted progressive image prefix can be checked; their actual
observation still has no accepted output hash. These expected sizes and
RSS/expected-size diagnostic ratios are never substituted for observed
admission claims.
`resource-results.json` retains source/tool/input/output hashes, repetitions,
individual observations, median times, peak RSS, thresholds and explicit
failures. Positive records also report typed-output/input-byte expansion and
peak-RSS/typed-output-byte ratios, and tile cases report selection/full RSS.
These are diagnostic amplification ratios, not new resource guarantees or
post-measurement thresholds. The larger grayscale fixture exercises
whole-image output/serialization growth; the 256-tile fixture makes fixed
per-process/tile metadata overhead visible even for tiny selected outputs;
HT JPIP additionally exercises reconstruction/hex-observation storage.
Their exact-output, unchanged RSS/time and tile/full-ratio gates are actionable
regressions without pretending typed output accounts for those other costs.
Unavailable default tooling/platform support blocks the gate;
explicitly configured missing tools and absent measurements cannot pass.
Failed inputs are preserved under ignored `resource-failures/` and uploaded
by CI. `all` does not implicitly invoke this Linux-specific gate; CI calls it
separately. `--subject` selects a trusted prebuilt binary; `--no-build` uses
the existing release harness.

## Technical reference inventory

[normative-coverage.json](normative-coverage.json), validated by
[its schema](normative-coverage.schema.json), is a maintained input under
`validation/`, not a generated report or implementation-progress record.
Its source-reference paths remain relative to the repository root.
It is a static inventory of topics and implementation,
specification, executable contract, proof/view, and test references. Its
validator checks every present item, including contracts that ensure a listed
spec and are called by the claimed implementation. Shadow-only links fail.
For scalar contracts it recognizes both `ensures returns (...)` and a named
return value whose typed or natural-number equality directly names a listed
model, including contracts with a `requires` clause.
For checked slice stores it also recognizes an equality between
`(named_result, final(slice)@)` and a listed state-transition model. Complete
planar transitions can include multiple final outputs, with the explicit
`part2_composition_planes(final(colors)@)` projection for nested color vectors.
Every named mutable-reference parameter must occur in that final-state tuple;
an omitted alpha output or a duplicate color output cannot stand in for it.
Success-only `Result` relations must use the same named `is_ok()` value in
both the guard and the tuple. Scalar final values, such as the work counter,
must participate in that same relation; an unrelated guard, old counter or
omitted output is rejected.
Unrelated
return binders, pre-state-only tuples, missing final-state relations and mere
model mentions do not qualify. Functions taking mutable references must still
provide the complete final-state relation; a bare return equality cannot replace it.
This is a conservative source-link check, not a
replacement for Verus.
Same-file links are checked inside another listed, formatted function body;
the contract's own declaration, an unrelated function or an indirect caller
does not qualify as a direct same-file call. Unsupported formatting can fail
this conservative check; it is not a full Rust parser.
It does not assert exhaustive standards-clause coverage, exact progress
counts, phase completion, or conformance.

Each inventory validation reads a fresh source snapshot. Declaration,
owner-qualified header and caller-body indexes are shared only within that
invocation and discarded afterwards; source text is never cached across
validations by filename or modification time. Schema text is also read on
every call. A bounded 32-entry cache avoids repeating meta-schema checks only
for identical schema contents; every supplied instance is still validated,
and changed or invalid schema contents are checked afresh. Mutation tests
retain all existing contract/input/state/consumer rejection cases and
explicitly check same-process source and schema changes.

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

After the actual pinned whole-crate Cargo-Verus command in
[PROOFS.md](../PROOFS.md#reproduce-verification):

```sh
.venv/bin/python validation/generate-proof-coverage.py target/validation/cargo-verus-output.log
.venv/bin/python validation/run-validation.py schemas
```

The default report is `target/validation/proof-coverage.json`; `--output-dir`
selects another directory. The collector writes normalized `verus-result.json`
and a schema-v3 report identifying `cargo verus verify`, `src/lib.rs` and
the exact `jpeg2000_decoder` crate namespace. It requires one root JSON result,
the pinned commit, whole-crate success, zero errors, nonempty project results,
and no termination bypasses or trusted proof escapes. A Cargo exit code, a
dependency proof or cached build output is insufficient; module-only `focus`
results are deliberately rejected. Raw Cargo output and normalized result
are separately hashed. It does not compare against
committed progress output or infer coverage for absent functions. CI retains
the stable release's `--no-lifetime` boundary explicitly; lifetime verification
is not claimed.

The Cargo package is `jpeg2000-decoder`; its Rust namespace is
`jpeg2000_decoder`. Existing corpus/profile/generator and oracle subject IDs
are stable validation-protocol identifiers, not Cargo package names. They
remain unchanged so old corpus and oracle configurations remain comparable.
Historical source-bound proof reports retain their original namespace.
