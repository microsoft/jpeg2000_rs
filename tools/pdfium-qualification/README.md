# Original JPEG2000 / PDFium integration qualification

This is the actual portable handoff of the original **310-image x eight
configurations / 41-PDF gate**, not an authorized replacement corpus.
The runner, manifests, custom consumer, expected outcomes and source patches
are public here rather than referenced through an inaccessible evaluator path.

## What is supplied

- `frozen/cohort.json`: all310 input requests and41 PDFs, with exact hashes,
  source IDs, actual indexed PDF context and generated-wrapper identities.
- `frozen/configurations.json`: the exact2,521 logical request configurations.
- Original three-backend output/status/pixel-hash decisions, independent
  reference adjudications, timing selection/measurements and audit receipts.
- The real PDFium consumer (`consumer/jp2_eval.cpp`) and complete overlay
  against public PDFium, including shim and Rust/CXX integration and truly
  non-strict full-page JPX calls. Original throwaway diagnostic probe targets
  are omitted; timed consumer code is unchanged.
- The original native-O3/final-ThinLTO-O3 patch and portable GN configuration.
- The34 original first-party generated encoded fixtures:16 synthetic JP2s,
  four HT encodings and14 tiny crate-validation streams. These are exact
  bytes, not re-encoded approximations.
- Portable public-input materialization, original runtime functions, the
  configuration replay, native flag audit and base/head outcome comparison.

Absolute machine paths and temporary pixel locations are removed from the
frozen JSON projections. The original manifest byte SHA is retained in
`frozen/provenance.json`; do not claim the portable projection has the same
file hash. IDs, dimensions, flags, encoded and pixel hashes are unchanged.
The original narrative and TSVs are retained under `frozen/`.

## Proven source/corpus identity

- Public PDFium:
  `68f43efa71ac66ba843ba286bb76d075aa1c49df`.
- Public `pdfium_tests` corpus:
  `2bcc4fdc9abe4c4c115c82c486ac4c46f1d474c5`.
- Public Hayro:
  `e7ada1354dff4041cdeed3d8ba56fe01b6186132`.
- Historical measured Rust main:
  `a99ab056b20b48a58a3eda23a89e4f3f6ec042b8`.

The original integration commits were local children of the public PDFium
base. `consumer/integration.patch` transfers them and the evaluation overlay;
there is no requirement to fetch an unpublished commit from Google's remote.

All208 Hayro conformance streams were checked against public Git blob hashes.
Public PDFium/Hayro fixtures and PNG pixels are not vendored: fetch the exact
source revisions. The included generated noise/gradient inputs originate
from the first-party generator (`synthetic-generator.py`, seed42); HT and
validation bytes are frozen at their original hashes. Never regenerate using
another encoder version and silently substitute different encoded bytes.

## Materialize on any host

```sh
git clone https://pdfium.googlesource.com/pdfium.git pdfium-source
git -C pdfium-source checkout 68f43efa71ac66ba843ba286bb76d075aa1c49df
git clone https://pdfium.googlesource.com/pdfium_tests pdfium-source/testing/corpus
git -C pdfium-source/testing/corpus checkout 2bcc4fdc9abe4c4c115c82c486ac4c46f1d474c5
git clone https://github.com/LaurenzV/hayro.git hayro-source
git -C hayro-source checkout e7ada1354dff4041cdeed3d8ba56fe01b6186132
python3 -m venv qualification-venv
qualification-venv/bin/python -m pip install -r tools/pdfium-qualification/requirements.txt
qualification-venv/bin/python tools/pdfium-qualification/materialize.py \
  --pdfium pdfium-source \
  --hayro-tests hayro-source/hayro-jpeg2000/tests \
  --results qualification-results
```

Success requires exact equality of every original input/PDF hash, embedded
payload/context/dimension multiset and logical manifest field. The native
resource templates and other source cases must not be dropped if damaged-PDF
warnings occur. There are21 existing PDFs plus20 generated wrapper PDFs.
Do not treat malformed-source parser warnings as a new corpus definition.

## Configure the actual consumer

Prepare a **disposable** PDFium checkout at the public base with its original
DEPS, Linux ARM64 sysroot and Rust/CXX build dependencies, following PDFium's
gclient instructions (`checkout_rust = True`). The fixture-only clone above
does not contain every build dependency. Never apply this to a user's worktree.

```sh
python3 tools/pdfium-qualification/configure.py \
  --pdfium /absolute/disposable/pdfium \
  --crate /absolute/exact-jpeg2000-checkout \
  --clang /absolute/clang-prefix \
  --rust /absolute/chromium-rust-prefix
cd /absolute/disposable/pdfium
third_party/ninja/ninja -C out/Openjpeg -j 4 jp2_eval
third_party/ninja/ninja -C out/Shim -j 4 jp2_eval
third_party/ninja/ninja -C out/Ffi -j 4 jp2_eval
```

Original toolchains were matching Clang24/Chromium Rust1.101.0-nightly LLVM24:
Clang `c3223914b50811fb3be915840f06456acb83d096`,
rustc `41b321963cf979d564d4bb447d9a09347664659f`.
Native N2 results and other native ARM/x86 evidence remain separately labeled.
Do not silently rebrand another host/toolchain as the original N2 experiment.
`--prepared` is only for an exact disposable original-consumer copy.

The overlay supplies per-build core/CAPI source roots. The C and Rust halves
of a shim must come from the same exact checkout, including private ABI v3
changes; the consumer itself calls public OpenJPEG-compatible entry points.
Do not link a new Rust half to an older C shim. The direct FFI bridge retains
the original packing/color behavior, not an implied correctness superset.

```sh
python3 tools/pdfium-qualification/audit.py \
  --work /absolute/disposable/pdfium \
  --crate /absolute/exact-jpeg2000-checkout \
  --output qualification-results/build-audit.json
```

The audit checks actual last O3/native/ThinLTO/NDEBUG C/C++ flags, native
opt3/one-codegen-unit Rust settings and linker-plugin LTO, final`--lto-O3`,
the actual lenient page macro, and byte-identical same-revision core archives
between shim and direct FFI. No fast-math, PGO, deadline instrumentation or
changed decoder feature/limit policy is silently introduced.

## Execute the exact original integration gate

```sh
qualification-venv/bin/python tools/pdfium-qualification/run.py functional \
  --results /absolute/qualification-results \
  --openjpeg /absolute/disposable/pdfium/out/Openjpeg/jp2_eval \
  --shim /absolute/disposable/pdfium/out/Shim/jp2_eval \
  --ffi /absolute/disposable/pdfium/out/Ffi/jp2_eval
```

The exact eight image requests are strict/lenient at reduction0,1,2 normal
color, and strict/lenient at reduction0 indexed. **All41 full PDFs request
genuinely lenient decoding at PDFium's real page call site.** Passing false
only to a standalone CLI does not change rendering. Every OpenJPEG control
status and successful packed-pixel hash must match the frozen original.

The portable transfer was actually executed against all three original
consumers: **2,521 requests / 7,563 outcomes reproduced exactly**, including
geometry/color and pixels. Exact input materialization and ten independent
reference controls also pass. See `frozen/bundle-verification.json`.
This validates the transfer, **not an untested performance PR head**.

Run base and candidate in separate result directories with the same materialized
cohort. Historical Rust results are not a substitute for each current PR base.

```sh
python3 tools/pdfium-qualification/compare_runs.py \
  --base /absolute/base-results \
  --candidate /absolute/candidate-results \
  --output /absolute/base-candidate-gate.json
```

Every changed outcome is retained as `REVIEW_REQUIRED`, not silently waived.
Additional main fixes, original intentional refusals, CDEF/ICC limitations
and C++-incorrect reference cases need their own documented dispositions.
The scope is packed8-bit consumer pixels, not native high-bit-depth equality.

## Independent references and timing

Use the same binary arguments for the `references` phase, plus
`--hayro-tests /absolute/hayro-source/hayro-jpeg2000/tests`.
This retains the POC cases where Rust agrees with independent pixels and
OpenJPEG differs; OpenJPEG is not an infallible oracle.

The `performance` phase uses the original65-workload selection, three rotating
rounds, three warmups, seven timed image or five PDF repetitions, CPU2.
Input loading/startup/writes/library initialization are excluded from timing.
Image contexts/packing/destruction and actual fresh-document rendering are
included. Known embedded images must preflight successfully before a PDF can
qualify. Omitted/white images are never a speedup.

Use RLIMIT_DATA=2GiB, not RLIMIT_AS; preserve actual decoder limits, strict/
compatible routing, input/output shapes and allocator/CPU budgets. Record
all adverse performance/tail observations, not only successes or medians.

## Authority and licensing

Supplying the original gate does **not** authorize merges, waive proof/package/
performance checks, or resolve required owner tradeoff decisions. No merge
authorization was assumed in this asset transfer. Unresolved candidates remain
unmerged; #470/#482 remain parked. No release/backport is implied.

Added harness/helpers and first-party generated fixtures are covered by this
repository's license. The PDFium patch retains upstream BSD notices; public
third-party fixture/oracle licensing stays with its original projects.
