# Native final-consumer results for #449

## Disposition

The standalone Cargo-consumer investigation is implemented and measured.
**Keep #449 open:** actual zune-image/PDFium final-workspace qualification is
still unavailable, and no deployment CPU-fleet compatibility claim is made.
Nothing here changes decoder runtime/spec/proof sources, package defaults,
release metadata or publisher settings. The early-MPS candidate was not used.

Do not recommend these settings as a universal decode-speed fix. On this
cohort, individual CPU tuning, ThinLTO and CGU=1 do not improve our aggregate
decode time. The combined setting improves ARM64 by about 2.8%, but does not
improve x86-64. This is not an explanation for a roughly 5.5–6.2× direct-API
gap to the scalar comparator.

## Source and execution binding

* PR: [#450](https://github.com/microsoft/jpeg2000_rs/pull/450).
* Final manual run:
  [44825727854](https://github.com/microsoft/jpeg2000_rs/actions/runs/44825727854),
  measurement commit `c96b7d1cc99b92136d97fdbe7d5d3ff50a3dcc7b`.
  Both optional native jobs succeeded. Normal test/MSRV/quality/native-numerics
  jobs are green; the generated decoder-validation gate remains unchanged,
  with its observed status recorded in `run-manifest.json`.
* Native x86-64: `ubuntu-latest`, **4 vCPUs, AMD EPYC 9V74**.
  Native ARM64: `ubuntu-24.04-arm`, **4 vCPUs, Neoverse-N2**.
  These are observed `lscpu` results, not assumed runner specifications.
  Neither result is emulated or a cross-build timing.
* Rust **1.93.1**, committed consumer lockfile; independent final executable
  for current-main, published 0.2.2 and Hayro 0.3.5 scalar.
* Current control: `97d5162b3f43fb14942c46bbea73752d26fb24b4`.
  Published source anchor: `4989f9c680beeb7bad4fbfd441a93aa373d2ba4f`;
  `.crate` SHA256:
  `9174c2cd54f8ba9401d48f3a71bc162dd999eacf7409662bc3339ddbe7d8cbcc`.
  Every runtime/spec/proof source-file hash matched between these controls.
* Canonical manifest SHA256:
  `5c33c9699031796f293e4cb5357c56748367793cbd21c59e7ddaba219069c954`.
  All **24 compressed inputs and four integer-generated PNM sources** match
  the parent-frozen cohort. Only eight synthetic JP2s are checked in; raw J2Ks
  are exact extracted codestreams. No private/PDF inputs were added.
* Each host completed **30 fresh-target builds and 2,304 new-process decode
  observations**: two reversed build rounds, four opposite-order decode
  pairs, five configurations, three backends, 24 inputs.
  All observations and outcomes are retained, including unqualified Hayro
  configurations. Headline decode aggregates use the 16 generated JP2/J2K
  inputs; the eight tracked inputs are separate acceptance probes.

Complete flags, actual final rustc/linker invocations, compiler/LLVM identity,
CPU flags, kernel/image, source hashes and process samples are in the
[raw archives](#persistent-evidence). See [README.md](README.md) for reproduction
and exact timing/API boundaries.

## Decode time and uncertainty

Positive means a **decode-time reduction**, not a throughput percentage.
Current-main intervals are 95% matched-pair bootstrap percentile intervals,
resampling four pair blocks, not individual iterations or 16 independent
images. JP2/J2K copies are correlated. Four pairs support an exploratory
observation, not a population-wide guarantee.

| Host | Configuration | Current-main reduction, % [95% interval] | Published 0.2.2 reduction, % |
|---|---|---:|---:|
| EPYC 9V74 | CPU only | −2.35 [−2.77, −2.02] | −1.98 |
| EPYC 9V74 | ThinLTO only | −0.43 [−0.73, −0.05] | −0.12 |
| EPYC 9V74 | CGU1 only | −3.24 [−3.69, −2.78] | −2.42 |
| EPYC 9V74 | Combined | −0.81 [−0.93, −0.67] | +0.03 |
| Neoverse-N2 | CPU only | −0.20 [−0.54, +0.21] | +0.10 |
| Neoverse-N2 | ThinLTO only | −0.03 [−0.24, +0.21] | −0.32 |
| Neoverse-N2 | CGU1 only | −2.66 [−2.98, −2.33] | −2.66 |
| Neoverse-N2 | Combined | +2.78 [+2.30, +3.26] | +2.64 |

CPU is `target-cpu=native`; all other settings are held fixed in each
one-factor comparison. Combined is CPU + ThinLTO + CGU1; it is not evidence
that any individual factor produced its gain. Per-input extremes also matter:
CPU-only regresses a current-main x86 noisy RGB lossless case by 6.42%;
CGU1 regresses an ARM noisy gray lossy case by 6.01%.
The ARM combined setting improves the generated per-input geometric ratios
by 0.56–4.00%; this does not establish a universal consumer/default policy.

The earlier complete ARM run
[44823353147](https://github.com/microsoft/jpeg2000_rs/actions/runs/44823353147)
independently observed +2.70% combined reduction, and no individual-factor
gain. Its raw data is retained, but is not pooled into the final intervals.

## Build, final native link, executable size and memory

Current-main final consuming executable; two reversed cold-target builds.
Build values are the observed min–max, not a confidence interval from `n=2`.
Final-link values are medians for the **one final executable's native cc
invocation**, excluding build-script links. All cc invocations and their sum
are also retained. Rustc performs LLVM ThinLTO before cc; this is not isolated
LLVM optimization time. Rustc wall/RSS observations retain that work.

| Host | Config | Build wall, s | Final cc, ms | Unstripped ELF, bytes | `.text`, bytes | Peak build single-process / sampled summed-tree RSS, MiB |
|---|---|---:|---:|---:|---:|---:|
| x86 | generic | 11.17–11.43 | 26.4 | 4,589,624 | 729,542 | 515.5 / 611.5 |
| x86 | CPU | 11.07–11.23 | 25.6 | 4,580,872 | 728,630 | 516.4 / 660.6 |
| x86 | ThinLTO | 11.51–11.69 | 23.9 | 2,624,456 | 715,318 | 514.8 / 645.4 |
| x86 | CGU1 | 14.15–14.44 | 25.0 | 4,516,136 | 704,310 | 540.2 / 657.2 |
| x86 | combined | 14.22–14.61 | 18.9 | 2,544,408 | 703,190 | 544.8 / 667.8 |
| ARM | generic | 16.14–16.19 | 115.0 | 4,547,352 | 621,512 | 532.4 / 635.4 |
| ARM | CPU | 16.30–16.40 | 114.7 | 4,547,080 | 633,752 | 513.8 / 618.7 |
| ARM | ThinLTO | 16.32–16.40 | 75.7 | 2,612,064 | 607,928 | 542.8 / 676.2 |
| ARM | CGU1 | 20.47–20.70 | 104.1 | 4,453,160 | 593,336 | 529.8 / 654.7 |
| ARM | combined | 20.24–20.25 | 63.8 | 2,561,440 | 593,944 | 520.9 / 644.9 |

**Size caveat:** the roughly 43% ThinLTO **unstripped file-size** reduction is
not a 43% code-size or stripped-production-artifact reduction. Prebuilt Rust
standard-library debug sections remain even with consumer debug=0.
The measured `.text` reduction is only **1.95% x86 / 2.19% ARM**.
Do not transfer the raw ELF result to an actual stripped zune/PDFium artifact.

The largest observed current-main decode-process RSS is **353.9 MiB x86 /
353.4 MiB ARM**, essentially unchanged by settings. These are GNU-time
process peaks, including startup, compressed input and post-timing sample
fingerprinting; they are not isolated decoder-owned allocation peaks.
The corresponding generic Hayro process peaks are 38.0 / 37.5 MiB, but its
u8 API and fingerprinting footprint differ; this is not adapter-identical
memory accounting.
Per-input/backend/config medians/maxima, link RSS and both build rounds
are retained. Summed-tree build RSS is sampled every 50 ms across all threads'
children, can miss peaks and can double-count shared pages. Shared hosted
CPU/OS cache state and instrumentation overhead remain measurement limits.

## Exact outputs and comparator qualification

Our current-main and 0.2.2 controls have **identical acceptance classifications,
dimensions and every sample fingerprint**:

* across all five build configurations and repeated observations;
* between published/current controls;
* across native x86-64 and ARM64, for all 24 fixtures × five configurations.

Every generated lossless output independently recovers its integer source
sample SHA256. These checks do not use Hayro as an oracle.

Hayro 0.3.5 uses default-features=false, `std` only. Its API, shape and lossless
source recovery worked on both hosts. However:

* On x86, CPU and combined settings change **all eight lossy-input**
  fingerprints relative to generic. These configurations' headline Hayro
  reductions and current/Hayro ratios are **null/unqualified**, not speed wins.
* Generic/ThinLTO/CGU1 Hayro lossy fingerprints also differ across
  architectures; CPU/combined x86 fingerprints match the ARM variants.
* Hayro and our outputs differ on the lossy inputs even at generic settings.
  No lossy numerical adjudication or pixel-oracle claim is made.

All variants, flags and hashes are preserved in
[`cross-native-outcomes.json`](results/cross-native-outcomes.json) and each
archive's `samples.jsonl`/`outcomes.json`. These observations do not establish
which lossy result is more accurate.

| Configuration | x86 current/Hayro geomean time ratio | ARM current/Hayro geomean time ratio |
|---|---:|---:|
| generic | 5.482× | 6.244× |
| CPU | unqualified: changed Hayro samples | 6.103× |
| ThinLTO | 5.460× | 6.263× |
| CGU1 | 5.632× | 6.283× |
| combined | unqualified: changed Hayro samples | 5.939× |

These are **direct-API performance comparisons**, not pixel-equivalence,
backend-paired uncertainty estimates or reproductions of the original
zune-image integration. Our API produces typed planar 64-bit samples; Hayro
produces normalized interleaved u8. Our extra interleave/hash is outside the
decode timer. Interpret the remaining gap accordingly.

## Consumer recommendation and residual acceptance

Retain the generic portable release baseline. Do not select host-specific CPU
flags or CGU1 as a universal optimization. A controlled ARM consumer may test
the combined setting, accepting its roughly 25% build-time increase for a
small cohort-specific decode gain. ThinLTO can be tested independently for
modest code-size benefits, but validate the **actual stripped final artifact**;
it has no meaningful decode gain here.

No actual zune-image application workspace or PDFium GN/C++/Rust final link
configuration was supplied. The similarly named local `zune-hayro-compat`
directory is another decoder worktree, not a zune consumer application.
The repository's experimental OpenJPEG C adapter is also not a PDFium build
and has different buffer-allocation boundaries. Actual consumer profile/
linker propagation, end-to-end output acceptance, performance, memory and
supported-CPU execution remain the concrete residual acceptance item.
The generic final-workspace recipe is tested evidence, not substitute coverage.

## Persistent evidence

[`results/`](results/) contains checked-in deterministic archives and SHA256
sidecars, plus readable derived summaries and the exact cross-native audit:

| File | Meaning |
|---|---|
| `run-44825727854-x86.tar.gz` | Final complete x86 raw text; SHA256 `9e1655880a75bf2c3093f9a31f9fabdcebe5b0549b23cb011d95b5408c7e53ad` |
| `run-44825727854-arm.tar.gz` | Final complete ARM raw text; SHA256 `5099ac3877328e06a17b7cd114be645d73a54895a2c04461b7097f5a26a0a5a2` |
| `run-44825727854-*.summary.json` | Derived original paired summaries plus exact final-consumer cc link and `.text` extraction |
| `attempt-44823353147-x86.partial.tar.gz` | All 102 pre-stop samples and 30 builds from the first detected Hayro drift; explicitly incomplete |
| `run-44823353147-arm.initial.tar.gz` | Earlier complete 2,304-sample ARM repeat; not pooled |
| `run-manifest.json` | Source, run/job/artifact IDs, archive hashes and explicit residual acceptance |

Every archive has a checksum index of **all** raw metadata/compiler/flags/
build/link/process/outcome text. Native executable bytes are excluded from
the compact checked-in archives, but their sizes/hashes are included.
Full hosted artifacts (30-day retention) also contain all native executables:

* [x86 artifact 14674548585](https://github.com/microsoft/jpeg2000_rs/actions/runs/44825727854/artifacts/14674548585)
* [ARM artifact 14674977659](https://github.com/microsoft/jpeg2000_rs/actions/runs/44825727854/artifacts/14674977659)

Earlier run `44822409433` rejected the existing general helper's actual
OpenJPEG 2.5.0 before timing. Run `44822702787` rejected nonidentical native
2.5.4 lossy re-encodings before timing. The frozen distribution fixes both
without changing any parent-frozen compressed input or source hash.
The earlier `44823353147` summed-tree RSS sampler omitted Cargo worker-thread
descendants; that field is invalid in its archives and is **not** used above.
Its GNU-time single-process RSS and raw timings remain separately available.
