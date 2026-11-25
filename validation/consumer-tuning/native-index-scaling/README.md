# Native fixed-pixel COPY-index qualification (#481)

This optional cohort preserves the **same frozen first-party 32×32 seeded
pixels and encoded bytes** used for the local index scaling investigation.
It is not the 32×1 constant selected-parts cohort, historical 310×8/41-PDF
handoff, 65-workload gate, publication approval or a claim of a universal win.
In particular, local K256-interleaved negative observations are not discarded.

## Exact source and dispatch guards

Only this ordered pair is admitted by `native_index_scaling.py`:

* baseline `f4b2b7b29d38fa31bd74263913462bb67d6e5e4e`;
* candidate `2743436c341a679ce62162f3fc3ef72807b98dee`.

The existing selected-parts helper additionally accepts this exact pair,
without changing its historical defaults or either earlier approved pair.
Unlisted pairings fail before source/tool setup or output creation. The
existing native Linux host/compiler/ELF, Cargo configuration, clean source
and upstream-origin checks remain active. Both source commits must be
reachable from **upstream repository branches** when dispatched: merely
having a local object, tooling ref or PR merge ref is insufficient. There
is no local-source exception. Publishing/reviewing those refs is the parent's
separate decision; this tooling does not push anything.

After independent tooling/runtime review and parent-authorized upstream
reachability, dispatch from the tooling branch, not a frozen runtime ref:

```sh
TOOLING_REF=tooling/native-index-481-qualification
gh workflow run ci.yml --ref "$TOOLING_REF" \
  -f consumer_benchmark=true -f consumer_benchmark_scope=native-index-scaling \
  -f native_baseline=f4b2b7b29d38fa31bd74263913462bb67d6e5e4e \
  -f native_candidate=2743436c341a679ce62162f3fc3ef72807b98dee \
  -f native_pairs=8
```

The dedicated job uses the existing pinned checkout/Python/upload actions
and separate **native** `ubuntu-latest` x86-64 / `ubuntu-24.04-arm` ARM64
hosts. The exact existing Rust 1.93.1 O3/native/ThinLTO/cgu1/System source
builder is reused; no cross compilation, new executor or profile override
is introduced. Scaling accepts exactly **eight pairs**. Other native scopes'
defaults and 8/24 choices remain unchanged.

To run the separate old selected-parts cohort against the new approved pair,
use the same dispatch with `consumer_benchmark_scope=native-selected-parts`
and the same explicit source IDs. That scope retains its original two
warmups plus **one 512-call timed batch**, not this six-call recipe.

## Frozen bytes and independent oracle

The repository's [MIT license](../../../LICENSE) covers these self-authored
inputs. No encoder or external codec dependency is installed or run by the
helper. [`../native-index-scaling-cohort.json`](../native-index-scaling-cohort.json)
records every actual file length/hash, K/P, physical order and original
encoder output hash, plus the seed and original encoder argv/provenance.

* PGM: `seeded32.pgm`, SHA-256
  `2d90e72ea5bacbac55fd8bdef05309f54beca92e52977939eef1d79295d58fd9`.
* Seed `0x48103232`; update
  `state=(1664525*state+1013904223) mod 2^32`, sample `state>>24`,
  raster order: 1,024 samples, 249 distinct values.
* Existing pinned OpenJPEG **2.4.0** encoder SHA-256
  `8b0901e43e2bf72cba2748183f032dfe5064b1dec8082b3b93e2eb1ee3597c71`;
  actual `-n 1 -r 4,2,1 -p LRCP -TP L`, tile sides 32/16/8/4/2/1.
* Actual K=1/4/16/64/256/1024; actual P=3/12/48/192/768/3072.
  Complete SOT/Psot parts were reordered only globally. Per-tile part bytes
  and order, main header and EOC are identical between each physical pair;
  no TLM/PLM/PLT/PPM/PPT or offset-dependent input is substituted.
* Frozen observer-free probe SHA-256
  `7a7fdba84ad8299a5825d46d8b054424d83cc914736893124613fcf1a31cb216`.
* Frozen cohort-manifest SHA-256
  `a39c347e707e1c68af82644b7465fe1c808129a31ab0c0216361da4715ce0297`.

The helper rechecks byte hashes, actual physical SOT/Psot count/order and
per-tile byte identity without rewriting or re-encoding. Its **independent
Python oracle** reconstructs the seeded PGM samples and checks the complete
`TypedImage` literal: every sample, image/component extent and origin,
precision/sign, subsampling/registration and empty CDEF. The 12 full-image
paths and K1024 interleaved `(31,31,1,1)` last-pixel ROI form exactly 13 cases.

Each native architecture must pass **all 26 full literal preflights** before
any of its **208 timed children** start. Every timed child makes exactly six
complete `decode_codestream_selected` calls: first literal-checked output,
one warmup, one calibration, three fixed decode-and-drop clocks. No adaptive
iterations or 512 batch is used. Thus each host has 1,248 calls in timed
children, plus 26 separate preflights. Input reads/startup/output checking
are outside the three API clocks; GNU time metrics cover each whole child.

Case order is deterministically shuffled by pair; backend order reverses in
alternate pairs. Summaries reuse native comparison conventions:
**candidate/baseline** ratios with matched-process-median bootstrap intervals
and pooled fixed-clock tails, without exclusions. Do not mix the opposite
ratio convention or 512-batch statistics from the selected-parts scope.

## Evidence and focused helper controls

Artifacts are named
`native-index-scaling-{arch}-{run_id}-{attempt}` (30-day retention).
They retain the exact probe/input/provenance bytes, source commit/tree/blob
records, compiler/profile/raw argv, recorded native ELFs and hashes,
all 26 literals, every process order/work record, stdout/stderr and
CPU/RSS/fault/context-switch metrics. Paths use portable safe components.
Architectures/cohorts are never pooled; every negative and outlier remains.

Focused source-only tests (no codec build/timing) cover source-pair guards,
both host architectures and mismatches, actual matrix/order, altered full
sample/CDEF rejection, six-call parsing, 208-child dispatch and artifact
paths/recorded ELF identities. Run them under any required shared validation
lock:

```sh
PYTHONPATH=validation/consumer-tuning python3 -B -m unittest \
  test_native_comparison test_native_selected_parts test_native_index_scaling -v
```

An untimed hosted/native qualification uses the same helper with
`--qualify-only`; normal workflow dispatch runs preflights and then all eight
pairs. No result or dispatch grants merge/adoption/publication authority.
