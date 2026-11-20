# Final-consumer build qualification (#449)

This is a **standalone final Cargo consumer**, not a change to the decoder's
release profile, supported CPUs, publisher settings or verification boundary.
It selects exactly one linked backend per executable:

* `current`: Git revision `97d5162b3f43fb14942c46bbea73752d26fb24b4`;
* `release022`: published `jpeg2000-decoder =0.2.2`, archive SHA256
  `9174c2cd54f8ba9401d48f3a71bc162dd999eacf7409662bc3339ddbe7d8cbcc`,
  source anchor `4989f9c680beeb7bad4fbfd441a93aa373d2ba4f`;
* `hayro-scalar`: `hayro-jpeg2000 =0.3.5`, **default features disabled**,
  only `std` enabled. No `simd`, `image`, `moxcms` or `fearless_simd`.

The control revisions' `src/`, `specs/` and `proofs/` trees are identical.
The early-MPS candidate is neither built nor used.

## Reproduce

On **native** Linux ARM64 or x86-64, from the repository root:

```sh
rustup toolchain install 1.93.1 --profile minimal
bash validation/consumer-tuning/build-openjpeg254.sh
python3 validation/consumer-tuning/generate_fixtures.py \
  --encoder target/consumer-tuning/encoder/build/bin/opj_compress
python3 -m unittest discover -s validation/consumer-tuning -p 'test_*.py' -v
# Untimed API/sample qualification (optional before remote runs):
python3 validation/consumer-tuning/smoke.py
python3 validation/consumer-tuning/run.py \
  --pairs 4 --build-rounds 2 --iterations 1 \
  --output target/consumer-tuning/results
```

The output directory must not already exist. The runner uses `cargo +1.93.1`,
the committed **consumer** `Cargo.lock`, `--locked --offline` after an untimed
fetch, two Cargo build jobs, and a fresh target directory for every cold build.
Rust dependencies are fetched before measurements; the first cold build can
still benefit later builds through OS filesystem caches. No cache-drop or
CPU/governor control is attempted on shared hosted runners.

For hosted hardware, explicitly dispatch the **existing registered** `ci.yml`
workflow at this branch, with `consumer_benchmark=true` and
`consumer_benchmark_pairs=4`. Its optional job uses `ubuntu-latest` and
`ubuntu-24.04-arm`, not cross compilation or emulation:

```sh
gh workflow run ci.yml --repo microsoft/jpeg2000_rs \
  --ref perf/consumer-build-tuning-449 \
  -f consumer_benchmark=true -f consumer_benchmark_pairs=4
```

Pushes/PRs never select the benchmark. Existing CI jobs and requirements remain
unchanged (including on manual dispatch). No publishing/tagging is involved.
Artifacts retain the entire cohort and raw evidence for 30 days; download them
for longer retention. `COMPLETE` is written only after all checks pass.

## Shared public cohort

`target/consumer-tuning/fixtures/manifest.json` is standalone; all its `path`
and `source` entries are relative to that directory. The checked-in
`cohort-v1.json` is the canonical expected manifest, SHA256
`5c33c9699031796f293e4cb5357c56748367793cbd21c59e7ddaba219069c954`.
Encoder executable SHA256 and help output are separate
`encoder-provenance.json` because native binaries differ by host.

Eight 1024×1024 cases cover smooth/noisy × gray/RGB × lossless/lossy.
Samples are unsigned u8, raster y/x/channel order, with these **integer-only**
patterns, evaluated for `y,x` in `0..1024`, `c` in `0..channels`:

* smooth: `((3*x + 5*y + 97*c) // 16) & 255`;
* noisy: reset 32-bit state to `0x6d2b79f5` for **each source**; for every
  sample execute `s ^= (s << 13) & 0xffffffff; s ^= s >> 17;
  s ^= (s << 5) & 0xffffffff`; emit `s >> 24`.

Expected **lossless source-sample** SHA256 (without PNM header):

| Source | SHA256 |
|---|---|
| smooth gray | `f8520a531141b470830eea83d515c20779e0af7f080c534af8a49b2e9bf2878d` |
| noisy gray | `9be4f35563ede119bb4a85dd735a75da95b2d815d83a28e257efa93296d384a7` |
| smooth RGB | `de85ac50140b4a439379457b0934e496aa22aff00628f2b3562d18f5147789c4` |
| noisy RGB | `d29168da35a4578465080abf504bf6336dfed729d6abf939495d27c0eded6122` |

OpenJPEG **2.5.4**, source revision
`6c4a29b00211eb0430fa0e5e890f1ce5c80f409f`, is invoked with explicit `-n 6`,
`-mct 1` for RGB / `-mct 0` for gray; lossy adds `-I -r 12`.
No tiles/precinct overrides or thread options are implicit benchmark knobs.
For each JP2, the raw J2K is the **exact extracted `jp2c` payload**, not a
second encoding. Manifest records source-file/sample hashes, encoded hashes,
COD resolution/MCT/wavelet fields, JP2 box hashes and concatenated non-codestream
metadata hash. Native regeneration must match **all** canonical fixture bytes.
The existing general `validation/build-openjpeg.sh` intentionally remains
unchanged: its pin is OpenJPEG 2.5.0, not the 2.5.4 encoder required here.

Eight already-tracked MIT/self-authored fixtures add small gray/RGB JP2,
minimal raw J2K, invalid raw SOC/JP2 signature, mixed-resolution RPCL,
odd-origin/single-row and missing-EOC acceptance cases. Their exact tracked
origins and licenses are in the manifest; adjacent MIT notices are copied.
No new private, external PDF or scraped corpus inputs are introduced.

## What is measured

All builds use opt-level 3, panic unwind, no debug info, no stripping, no
incremental compilation; only these factors vary:

| Configuration | `target-cpu` | release LTO | codegen units |
|---|---|---|---|
| generic | compiler target baseline | `false` | 16 |
| cpu | `native` | `false` | 16 |
| thinlto | compiler target baseline | `thin` | 16 |
| cgu1 | compiler target baseline | `false` | 1 |
| combined | `native` | `thin` | 1 |

`lto=false` is Cargo's ordinary release policy; rustc can still perform local
ThinLTO within a crate. `thin` here specifically enables **cross-crate** ThinLTO.
One-factor comparisons isolate CPU, cross-crate ThinLTO and CGUs; the combined
configuration is also measured, but this is not a full interaction factorial.
`native` means the **observed** hosted CPU, not an assumed Neoverse-N2.

* Two cold build rounds reverse the complete configuration/backend order.
  Final binaries, byte sizes, section sizes, ELF notes, full verbose Cargo
  logs, Cargo timing reports and **every rustc/native-cc invocation** are retained.
  The wrapper preserves Cargo jobserver descriptors.
* Build wall/CPU time and GNU-time peak single-process RSS are recorded.
  Summed process-tree RSS is sampled every 20 ms; it can miss peaks and
  double-count shared pages. It is not a cgroup memory/allocation bound.
* Link time is measured at the **native cc linker** boundary, with its own
  peak RSS. LLVM ThinLTO optimization runs inside rustc before native cc;
  retained rustc timing includes that optimization. These are not falsely
  described as isolated LLVM LTO-link time.
* Every decode observation is a **new process**, reading one input into memory
  before `Instant` starts. It times the complete selected decode API, not file
  I/O, output hashing, process startup or printing. No warmup is discarded.
  The default is one decode/process; if increased, all per-iteration times
  are retained, and statistical units remain process medians, not iterations.
* Our API returns typed planar 64-bit samples; Hayro returns interleaved u8,
  including its own normalization. Our optional interleave/hash is **outside**
  the decode timer. API/output footprints differ, so this is not an adapter-
  identical zune-image end-to-end comparison.
* Each tuning is directly paired with a fresh generic process on the same
  input/backend. Generic-first and tuned-first order alternate; outer tuning,
  fixture and backend orders reverse. Raw rows preserve pair/position, all
  outcomes and sample fingerprints. Nothing is filtered for speed.
* `summary.json` reports paired ratios, order-specific observations, per-input
  ranges, build/link/size/RSS and deterministic 4,000-resample 95% bootstrap
  intervals. Pair blocks, not individual timings, are resampled. Four pairs
  provide exploratory uncertainty, not a population guarantee; JP2/J2K copies
  of a source are correlated. Generic-vs-Hayro ratios are explicitly
  **not backend-paired**.

Every successful output records shape and fingerprints; errors preserve their
full Debug classification. Within-process, cross-config and cross-pair
fingerprints/acceptance must agree; main and release controls must agree too.
Lossless generated images must recover independently generated source bytes.
Hayro is **never a pixel oracle**; its lossless output must independently recover
the source, its API/layout must work, and lossy sample differences are recorded,
not adjudicated against Hayro. Tracked fixtures are acceptance probes, not
silently treated as comparable performance inputs.

## Consumer recommendation and remaining acceptance

Leave portable defaults unchanged. Host CPU tuning is valid only for a
controlled deployment CPU fleet; never ship a `target-cpu=native` artifact as
a generic portable binary. ThinLTO and CGU=1 are consumer-workspace choices:
measure them **individually**, then together, against build/link time, binary
size, memory and confidence intervals on the real deployment workload.

For a real final workspace, place profiles in its **root** Cargo.toml, not the
dependency manifest, pin its lockfile/toolchain, and build the actual executable:

```sh
CARGO_PROFILE_RELEASE_LTO=thin \
  cargo +1.93.1 build --release --locked -vv --bin YOUR_REAL_CONSUMER
# Separate experiment, not conflated with LTO:
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 \
  cargo +1.93.1 build --release --locked -vv --bin YOUR_REAL_CONSUMER
# Only for an explicitly controlled CPU deployment:
RUSTFLAGS='-Ctarget-cpu=YOUR_DEPLOYMENT_CPU' \
  cargo +1.93.1 build --release --locked -vv --bin YOUR_REAL_CONSUMER
```

Audit final rustc/link arguments, native ELF, adapter output and supported-CPU
execution; changing a library Cargo.toml is not evidence that these settings
reached the final executable.

**No actual zune-image or PDFium build workspace/configuration is supplied to
this investigation.** Their linkage (including any GN/Rust/C++ overrides),
portable-CPU execution and end-to-end performance remain explicit residual
acceptance items; this generic final-consumer recipe is tested evidence, not
a claim to have reproduced those builds. Hosted systems are representative
observations, not every supported CPU. Build tuning alone is not an explanation
for the previously reported large decoder gap. Do not close #449 until the
real-consumer and other remaining acceptance criteria are resolved.

See `RESULTS.md` for source-bound observed native runs once available.
