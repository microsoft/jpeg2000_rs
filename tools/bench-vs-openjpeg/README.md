# In-memory OpenJPEG comparison

This unpublished, dependency-free tooling reuses the repository's frozen MIT
synthetic corpus and provenance. It does not change decoder defaults.

## Output contract

The current crate's standard raw API returns `TypedImage`: planar unsigned
`u64` or signed `i64` samples, not an 8/16-bit interleaved buffer. The primary
measurement is that actual output. The C driver decodes from memory and converts
OpenJPEG's planar 32-bit samples to the same planar 64-bit representation inside
the timed interval. Its separate `native` measurements omit this conversion.
Rust's native typed output is already its primary output.

Both intervals include setup, header parsing, entropy, transforms, output
allocation/conversion, and decoder-internal cleanup. File reads, result
destruction, output comparison/serialization, and CSV writes are excluded.
Both drivers consume the completed output through an optimization barrier before
the end timestamp; the C barrier requires GCC or Clang.
Codec and stream objects are new per iteration; compressed bytes are read once.
All runs explicitly select one thread. The Rust API has no thread-count option;
`BENCH_OPENJPEG_THREADS` is only for separately labeled C-only diagnostics.
The runner sets `OPJ_NUM_THREADS=0` for codec construction, then the driver calls
`opj_codec_set_threads(..., 1)`. Setting both to one would create and destroy an
unnecessary first worker pool inside each timed iteration in OpenJPEG 2.5.4.

The common dump protocol contains little-endian 64-bit words: image width,
height, component count, then each component's width, height, precision,
signedness and raster samples, precision <=31. Drivers recognize the JP2
signature and select the public JP2 API/OpenJPEG JP2 codec; other inputs use
the raw codestream APIs. The image canvas is the reduced global grid, not
component zero's potentially subsampled dimensions. Components retain their
individual geometry. This is not an independent ICC/color-conformance oracle.
The original raw/unit-sampled timing binaries and hashes remain unchanged;
container-aware conformance drivers are rebuilt and reported separately.
Lossless results must agree with each other **and** the independently authored
source hashes. Irreversible results retain maximum absolute differences and
differing-sample counts; reference disagreement is not a new tolerance.

## Run

Requires native Linux, Rust >=1.88, a C compiler, CMake, Ninja or Make, Python
3.12, git, and taskset:

```sh
python3 tools/bench-vs-openjpeg/run.py --output /absolute/fresh/evidence
```

This builds the Rust consumer and a static OpenJPEG **2.5.4**, pinned to
`6c4a29b00211eb0430fa0e5e890f1ce5c80f409f`, and runs generic, consumer
(ThinLTO/cgu1), and native configurations. C uses Release/O3 and
`-ffp-contract=off`, including the timing builds. No fast-math is enabled.
Native is nonportable. Add `x86-64-v3` to `--configs` only on a native x86-64
runner. `CC`, `AR`, `RANLIB`, PATH and Cargo's target-linker environment variables
can select a local toolchain; use the **same** toolchain in all cells.

Useful options:

```sh
# A checked, existing clean reference checkout can avoid another clone.
python3 tools/bench-vs-openjpeg/run.py --output /absolute/fresh/generic \
  --configs generic --openjpeg-source /absolute/openjpeg-2.5.4 --cpu 3
# Same request in both libraries; these small inputs do not qualify the 8K class F.
python3 tools/bench-vs-openjpeg/run.py --output /absolute/fresh/reduced \
  --configs generic --case lossless --reduce 2
python3 tools/bench-vs-openjpeg/run.py --output /absolute/fresh/window \
  --configs generic --case lossless --window 128,128,512,512
```

Every process has three warmups and at least fifteen measured iterations
**and** two seconds of summed decode time. Two fresh-process rounds reverse
backend order. Medians/IQRs pool those process samples; raw round identifiers
allow checking drift. Differences inside combined IQRs are noise, not wins.
Keep CPU affinity the same and avoid concurrent owned measurement work.
Do not change global CPU settings on shared hosts.

`raw.csv`, `summary.csv`, `summary.md`, per-image correctness JSON, process
stdout/stderr, exact command lines, per-process wait4 max RSS/faults/CPU time,
compiler versions and binary hashes remain in the output directory.
`COMPLETE.json` appears only after the selected matrix succeeds.
Shorter `--iterations`/`--minimum-ms`/`--warmups` settings are for smoke tests,
not performance claims.

Coverage is deliberately explicit: eight 1MP smooth/noisy legacy streams and
three HT streams, including lossless/lossy and RGB MCT, reused without
re-encoding. This is **not** the requested complete natural-photograph,
12/16-bit, coding-mode, tiled/progression, large-window or conformance corpus.
The source/encoding recipes are in
[`validation/consumer-tuning`](../../validation/consumer-tuning/README.md).
Do not promote this subset's class geometric means to full A-G qualification.

## Expanded photographic and coding corpus

The optional preparer uses Pillow 12.0.0, outside the decoder package:

```sh
python3 -m pip install -r tools/bench-vs-openjpeg/requirements-corpus.txt
python3 tools/bench-vs-openjpeg/corpus.py --output /absolute/fresh/corpus \
  --assets /absolute/photo-cache --encoder /absolute/openjpeg254/opj_compress
```

It uses two hash-verified original NASA/JSC photographs with inspected
public-domain source pages, records credit/license and every encoding command/hash, and checks
actual SIZ/COD properties rather than treating encoder arguments as proof.
Inputs cover 1.5MP and 20.7MP RGB/grayscale; 12/16-bit derived gray; 10/40/100:1
9/7; 32/64 blocks and each mode switch; tiling, precincts, progression,
layers and thumbnails; and 8K gray. High-precision low bits are explicitly
synthetic, and 8K is resampled, not represented as native sensor capture.
`--groups ABCDF` can select preparation families.

Preflight every input with the same binaries before timing. The inventory
retains nonzero exits, crashes, stderr, output mismatches and numerical
differences; refused files are never counted as speedups:

```sh
python3 tools/bench-vs-openjpeg/qualify.py --manifest /corpus/manifest.json \
  --rust /baseline/generic/cargo/release/bench-vs-openjpeg \
  --openjpeg /baseline/generic/bench-openjpeg --output /fresh/qualification \
  --qualified-manifest /corpus/qualified-generic.json --cpu 3
python3 tools/bench-vs-openjpeg/run.py --output /fresh/expanded-timings \
  --corpus-manifest /corpus/qualified-generic.json --configs generic \
  --reuse-builds /baseline --openjpeg-source /openjpeg-2.5.4 --cpu 3
```

Qualification exits nonzero if any case fails, even though its full inventory
and accepted-subset manifest are saved. The latter is not full-cohort or
normative conformance qualification. Use matching `--reduce`/`--window`
requests in both commands. Independent lossless source hashes use interleaved
little-endian 8/16-bit samples; the decoded comparison stays planar 64-bit.
For zero-origin, unit-sampled window cases, `qualify.py --check-window-crop`
also decodes each input fully and checks its actual matching crop for each
backend separately. Any failure or mismatch prevents qualification; this is
not a post-crop performance measurement.
Both preflight and timed decoder processes have the same default 8GiB OS
address-space safety cap, recorded separately from unchanged library limits.
`--maximum-address-space` changes that tooling cap; zero disables it.
Use `--decoder-source /absolute/clean/committed/worktree` to build a separately
recorded decoder revision, such as a newer merged main. It cannot be combined
with `--reuse-builds`: an old executable must never be relabelled as new source.
The original frozen control and new-main measurements remain separate.

The expanded A-D matrix plus all three 8K streams at discard 1/2/3 and a
512-square window can be generated, fully inventoried and measured sequentially:

```sh
bash tools/bench-vs-openjpeg/expanded.sh FRESH_OUTPUT OPENJPEG_254_SOURCE \
  OPENJPEG_254_ENCODER CLEAN_DECODER_WORKTREE CPU PHOTO_CACHE
```

Its initial short build-check is explicitly not speed evidence. Any preflight
failure stops the command after saving the complete inventory, rather than
silently benchmarking only surviving files. Full protocol measurements then
use the exact hash-checked binaries for every request.
To resume only the 8K work after a completed build/timing matrix, without
repeating A-D:

```sh
bash tools/bench-vs-openjpeg/partial.sh COMPLETE_MATRIX MANIFEST \
  FRESH_PARTIAL_OUTPUT OPENJPEG_254_SOURCE CPU
```

The report branch also adds an opt-in `ci.yml` dispatch scope:
`consumer_benchmark=true`, `consumer_benchmark_scope=uncovered-evaluation`.
It pins decoder `f4b2b7b29d38fa31bd74263913462bb67d6e5e4e`, Rust 1.93.1
and OpenJPEG 2.5.4, and measures the smaller A-D inputs on native x86-64 in
generic, consumer, x86-64-v3 and native profiles. The 20.7MP and 8K inputs
are explicitly excluded from that hosted timing scope, not declared qualified.
No default CI behavior changes. Artifacts retain canonical encoded inputs,
raw observations, outcomes, metadata and v3 final-binary disassembly, not
build caches or full pixel dumps. Cross-host pooling requires matching input
hashes; independently regenerated lossy streams are not presumed identical.
The two small original NASA photographs are retained with their separate
[public-domain notice](assets/NOTICE.txt), credit and pinned hashes. Use
`--assets tools/bench-vs-openjpeg/assets` for offline preparation. Hosted
acquisition received HTTP 403; CI uses these same licensed bytes rather than
retrying through an alternate identity or weakening download hash checks.
The separate `uncovered-instructions` scope builds the same four configurations
and records Callgrind process instruction counts for one declared representative
of each A-D family. Its shortened build checks are not timing evidence.
Unsupported native ISA instructions remain recorded failures, never zero counts.
The `uncovered-candidate` scope requires `native_candidate` as a complete
same-repository commit SHA. It separately checks out that source, builds a
generic/v3 current-main control on the declared 57-case cohort, then measures
reversed-order baseline/candidate processes with the full protocol. Its short
control build-check clocks are not speed evidence. Three-repeat Callgrind
guest-instruction comparisons and final candidate disassembly remain separate.
No native/AVX-512 instrumentation is substituted for the explicit v3 row.
For a targeted confirmation, `uncovered_case` selects cases by regex; its default
preserves the full 57-case cohort. Include the four representative counter cases
when comparing their instruction counts. The selected regex is recorded in
the artifact, and baseline/candidate v3 disassembly is retained. Keep repeated
sessions separate and retain the original matrix, including any regressions.

`collect.py --work WORK --output FRESH_SIBLING_DIRECTORY` performs this
portable evidence collection with a hashed index and an explicit completion
indicator. It refuses to overwrite a collection or place it inside its source.
Build-cache detection is structural: a real configuration or case named
`consumer`/`cargo` must not be discarded. Completed collections are checked
for omitted per-process and instruction evidence before the index is issued.
For ambiguous backend stdout names, the captured process mode distinguishes
pixel dumps from instrumented `SAMPLE` text; filenames alone are insufficient.
This also applies to arbitrarily named original #299 baseline/candidate stdout;
the process metadata is retained even when its pixel stdout is omitted.

For a completed full-protocol matrix, independently verify all raw sample
counts/durations, worker/cap metadata, case coverage and reproducible summary
medians/IQRs, then extract source-separated latency, ratio, output-throughput,
numerical and resource tables:

```sh
python3 tools/bench-vs-openjpeg/analyze.py --matrix COMPLETE_MATRIX \
  --output FRESH_ANALYSIS
```

This rejects shortened build checks. Throughput uses the selected uniform,
unit-sampled cohort's decoded samples and channel count, not the full input
area for partial requests. These tables do not qualify a numerical tolerance,
missing stage attribution or normative conformance.

To rerun the available baseline, both committed isolated experiments, separate
profiles/counters, and reduced/windowed checks sequentially with one command:

```sh
bash tools/bench-vs-openjpeg/evaluate.sh /absolute/fresh/evaluation \
  /absolute/openjpeg-2.5.4 /absolute/c2-worktree /absolute/c12-worktree 3 \
  /absolute/original-numerical-299
```

The last argument is optional; omitting it does not qualify #299. Set `PERF`
when the profiler is not on PATH. This command does not claim missing corpus,
x86-64-v3, multithreading or proof qualification.

The external conformance inventory is separate and must not run concurrently
with owned timing. It downloads the pinned tree's 57 encoded conformance
vectors and two notices through GitHub CLI, verifies each Git blob and size,
retains the mandatory conformance-use COPYRIGHT, and records every backend
outcome under the same decoder address-space cap:

```sh
python3 tools/bench-vs-openjpeg/conformance.py --output FRESH_INVENTORY \
  --rust COMPLETE_MATRIX/generic/cargo/release/bench-vs-openjpeg \
  --openjpeg COMPLETE_MATRIX/generic/bench-openjpeg --cpu CPU
```

Set `--gh` if GitHub CLI is not on PATH. This command reports every difference
without inventing a lossy tolerance or normative oracle; it exits nonzero unless
all 57 outputs are identical. It does not cover the separately licensed/mixed
nonregression collection. Vectors are not committed, packaged or exported by
`collect.py`; only their hashes, outcomes and provenance are portable evidence.

For user-space hardware counters and profiles, use a separate counting run:

```sh
perf stat -e cycles:u,instructions:u,branch-misses:u \
  taskset -c 3 /path/to/driver INPUT typed 0 - 1 0 0
perf record -e cycles:u -c 5000000 --call-graph dwarf -o /path/to/profile.data -- \
  taskset -c 3 /path/to/driver INPUT typed 0 - 15 2000 3
```

These process counters include startup/input I/O; do not label them isolated
decode-stage counts. Instrumented profiling is separate from timing.

For the complete available baseline's separate attribution/counter collection:

```sh
python3 tools/bench-vs-openjpeg/profile_baseline.py \
  --baseline /absolute/evidence --output /absolute/fresh/profiles --cpu 3
```

It uses a fixed user-cycle sample period so OpenJPEG's short-lived single-worker
threads are sampled, rather than relying on per-thread adaptive frequency.
Stage buckets are approximate leaf-symbol attribution, not isolated stage
timers; unknown symbols stay unknown. Unsupported LLC counters remain explicit.
Process profiles include startup and destruction, unlike timed decode intervals.
The profiler follows the completed matrix's actual reduce/window request and
hash-checks original or reused binaries. `--config native` selects that
configuration; `--profile-iterations 1` bounds collection on long 8K requests
while retaining at least two seconds of sampled decoding. It does not shorten
or replace the separately validated uninstrumented timing protocol.

## Isolated variant qualification

For exact output/error regression against an expanded control, its selected
requests and an already acquired conformance inventory:

```sh
python3 tools/bench-vs-openjpeg/qualify_variant.py --candidate-source CANDIDATE \
  --baseline COMPLETE_FULL_MATRIX --partial COMPLETE_PARTIAL_ROOT \
  --conformance EXISTING_CONFORMANCE_INVENTORY --output FRESH_QUALIFICATION
```

This separately builds the container-aware generic driver, hashes every input
and complete output, and requires baseline refusals to preserve their exit
status and error text. Matching pixel stdout is removed only after comparison
and hash recording; mismatches stay available. Matching existing refusals is
regression evidence, not normative conformance.

After an isolated paired comparison, separate three-repeat process counters
can be collected using `count_variant.py --comparison COMPLETE_COMPARISON
--baseline COMPLETE_FULL_MATRIX --output FRESH_COUNTERS --perf PERF --cpu CPU`.
It verifies both executable identities, alternates process order and preserves
unsupported event markers; these are not timed-stage or uninstrumented samples.
Use `--counter-backend callgrind` where hosted hardware counters are unavailable;
its original profiles and parsed instruction counts are retained, and any tool
failure remains a nonzero result.

An isolated prototype can be compared without changing the baseline or stacking
other candidates:

```sh
python3 tools/bench-vs-openjpeg/compare.py --baseline /absolute/evidence \
  --candidate-source /absolute/clean/committed/prototype \
  --output /absolute/fresh/candidate-results --cpu 3
```

This builds the same consumer against the prototype, checks every output bit,
and repeats paired controls in generic and consumer profiles. Optional
`--numerical-299 DIRECTORY` checks the six original supplied controls and writes
per-image before/after differences. Supply those rights-cleared original inputs;
they are not silently replaced with similar generated images.
`--reuse-builds /absolute/evidence` on the main runner reuses hash-checked
binaries for additional reduced/windowed requests, not cached decoded images.

```sh
python3 -m unittest discover -s tools/bench-vs-openjpeg -p 'test_*.py' -v
cargo fmt --manifest-path tools/bench-vs-openjpeg/Cargo.toml -- --check
```
