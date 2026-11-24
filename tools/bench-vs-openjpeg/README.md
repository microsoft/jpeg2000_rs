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
Codec and stream objects are new per iteration; compressed bytes are read once.
All runs explicitly select one thread. The Rust API has no thread-count option;
`BENCH_OPENJPEG_THREADS` is only for separately labeled C-only diagnostics.

The common dump protocol contains little-endian 64-bit words: image width,
height, component count, then each component's width, height, precision,
signedness and raster samples. It is intentionally limited to the unit-sampling
raw corpus, precision <=31. It is not a JP2 palette/color compatibility driver.
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

For user-space hardware counters and profiles, use a separate counting run:

```sh
perf stat -e cycles:u,instructions:u,branch-misses:u \
  taskset -c 3 /path/to/driver INPUT typed 0 - 1 0 0
perf record -e cycles:u -F 199 --call-graph dwarf -o /path/to/profile.data -- \
  taskset -c 3 /path/to/driver INPUT typed 0 - 15 2000 3
```

These process counters include startup/input I/O; do not label them isolated
decode-stage counts. Instrumented profiling is separate from timing.

```sh
python3 -m unittest discover -s tools/bench-vs-openjpeg -p 'test_*.py' -v
cargo fmt --manifest-path tools/bench-vs-openjpeg/Cargo.toml -- --check
```
