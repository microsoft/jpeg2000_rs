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
python3 validation/consumer-tuning/generate_fixtures.py
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

The eight canonical self-authored JP2 files are checked into `frozen/` under the
repository MIT license. Preparation reconstructs integer source samples, checks
every frozen JP2 hash, extracts raw codestreams deterministically, copies the
tracked acceptance probes and reproduces the canonical manifest **exactly**.
It does not compile an encoder or re-encode benchmark inputs.

For optional source/encoder reproduction evidence, independently of timing:

```sh
bash validation/consumer-tuning/build-openjpeg254.sh
python3 validation/consumer-tuning/generate_fixtures.py \
  --encoder target/consumer-tuning/encoder/build/bin/opj_compress \
  --output target/consumer-tuning/reproduction
```

Native re-encodings and their equality/difference records are retained in a
separate `native-reencode/` directory, **never** substituted for timed inputs.
Lossless re-encodings must match; lossy bitstream differences are recorded.
Run `44822702787` observed two lossy cases differing between the original
GCC 11-built encoder and both hosted native encoders, even though their integer
source samples and OpenJPEG revision matched. Both hosted cohorts agreed with
each other. `frozen-provenance.json` records that observation and original encoder
hash/compiler/flags; independent floating-point encoders are not required to
produce identical lossy streams.

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
`archive_evidence.py RESULTS DESTINATION.tar.gz` creates a deterministic,
checksum-indexed archive of **all** raw textual observations for long-term
retention. Native executables are excluded from this compact archive, but
their sizes/hashes remain; the full hosted artifact also contains executables.
`--incomplete` is an explicit opt-in for a failed attempt; the archive index
marks it incomplete and records expected versus observed sample counts.
Keep generated archives, long summaries and run reports outside tracked
source, as required by [RELEASING.md](../../RELEASING.md#source-publication):
use ignored `target/consumer-tuning/` output or an external evidence store,
not `validation/consumer-tuning/results/`. The maintained
[evidence index](evidence.json) locates the accepted run, checksums, complete
host-local snapshot and exact hosted-artifact expiry dates. Hosted artifacts
expire after 30 days; the local copy also has no indefinite-retention guarantee.

## Shared public cohort

`target/consumer-tuning/fixtures/manifest.json` is standalone; all its `path`
and `source` entries are relative to that directory. The checked-in
`cohort-v1.json` is the canonical expected manifest, SHA256
`5c33c9699031796f293e4cb5357c56748367793cbd21c59e7ddaba219069c954`.
Original encoder executable SHA256/compiler/flags are in
`frozen-provenance.json`; prepared `encoder-provenance.json` also records any
optional native re-encoding evidence.

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
metadata hash. Prepared benchmark inputs must match **all** canonical bytes.
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
  Summed process-tree RSS is sampled every 50 ms across **all** process threads'
  children (Cargo spawns compiler children from worker threads); it can miss peaks and
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
not adjudicated against Hayro. A changed Hayro fingerprint is retained, not
silently filtered or allowed to abort measurements of our invariant controls.
Any affected Hayro tuning aggregate/comparator ratio is explicitly **unqualified**
(`null` headline reduction/ratio), while all its raw times and outputs remain.
Tracked fixtures are acceptance probes, not
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

### Supplied clean J2K integration follow-up

[Issue #449's reproducible handoff](https://github.com/microsoft/jpeg2000_rs/issues/449#issuecomment-7071726628)
now supplies an independently pinned zune adapter, harness, lock and historical
fixture recipe. See [the imported handoff](zune-handoff/README.md) and
[`zune_integration.py`](zune_integration.py). The optional workflow dispatch
scope `zune` builds the five isolated profile cells on native x86-64 and ARM64,
using one verified input cohort. This is separate from the earlier standalone
study and does not edit the shared workspace described below. Results are not
claimed until the actual-consumer matrix completes. PDFium uses GN and needs
its own direct-backend qualification.

### Historical shared zune workspace inspection

The actual git workspace **does exist** at
`/workspace/zune-image/zune-image` (the outer directory is only a wrapper),
HEAD `13edc8d07f1572f149f83c59cf861211042c9874`. A read-only follow-up found:

| Root profile | Declared settings |
|---|---|
| `release` | `debug = 2` |
| `dist` | `inherits = "release"`, `lto = "thin"` |

`crates/zune-image/Cargo.toml` has no JPEG 2000/Hayro/JP2/J2K dependency or
feature; a case-insensitive search of all workspace `Cargo.toml` files found
none. The benchmarks have no J2K entry. Thus the missing acceptance item is
the **actual J2K integration and end-to-end comparison harness**, not the
existence of a zune workspace. Its shared dirty lockfile and unrelated
incremental work were not edited, copied or published; no builds were run there.

For a final Cargo build **owned by that workspace**, its root profiles govern
workspace members and dependencies, including a decoder once integrated.
Dependency manifests' own profiles do not override the consuming root.
With no further profile/config/environment overrides, `--release` would use
release optimization with **debuginfo=2**; `--profile dist` would inherit that
debug setting and enable cross-crate **ThinLTO**, including final executable
link/codegen. Neither declaration selects a host-specific CPU or CGU1.
The benchmark here uses debug=0, so it is not an exact reproduction of either
declared zune root profile or its final binary size.

After an owner supplies a real J2K-integrated target/harness, a root-level
invocation would select the intended profile, for example:

```sh
# Templates only: no such J2K integration/target was qualified here.
cargo +1.93.1 build --manifest-path /workspace/zune-image/zune-image/Cargo.toml \
  --release --locked -vv --bin YOUR_REAL_J2K_CONSUMER
cargo +1.93.1 build --manifest-path /workspace/zune-image/zune-image/Cargo.toml \
  --profile dist --locked -vv --bin YOUR_REAL_J2K_CONSUMER
```

Verify the actual final rustc/link arguments, outputs and supported-CPU
execution; the declarations alone are not end-to-end qualification. If a
different application workspace consumes zune-image as a dependency, **that
application's** root profiles govern instead.

`/workspace/pdfium-dev` is absent, so no PDFium GN/C++/Rust final configuration
was inspected or qualified. Actual J2K integration/harness, GN/Rust/C++
linkage where relevant, portable-CPU execution and end-to-end performance/
memory remain residual acceptance items. Hosted observations do not cover
every supported CPU. Build tuning alone is not an explanation for the large
decoder gap. Keep #449 open until the real-consumer criteria are resolved.

See [RESULTS.md](RESULTS.md) for observed native results, all raw data and
explicitly unmet actual-consumer acceptance. Derived analysis can be written
without changing the original observations:

```sh
python3 validation/consumer-tuning/summarize.py PATH_TO_EXTRACTED_RESULTS \
  --output target/consumer-tuning/recomputed-summary.json
```
