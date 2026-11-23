# Actual zune-image consumer qualification (#449)

## Reproducible scope

The [supplied handoff](https://github.com/microsoft/jpeg2000_rs/issues/449#issuecomment-7071726628)
unblocked an owned, independent checkout at zune commit
`fa80e24b17ff388ac850d6042bdca391f9913c4e`, with its supplied adapter, executable
harness and lockfile. The measured decoder is **published 0.2.2**, not main
after #451/#457. Hayro is scalar 0.3.5. Neither shared workspace was modified.

[Native run 44970463577](https://github.com/microsoft/jpeg2000_rs/actions/runs/44970463577)
at `6ccff3fd058569ff602519c3b064874bb903dea7` completed on AMD EPYC 9V74
(`znver4`) and Neoverse-N2, with Rust 1.93.1:

* Five isolated cells: generic, CPU only, ThinLTO only, CGU1 only, combined.
* Two reversed build rounds: **40 fresh builds** across the two hosts.
* Four reversed process pairs per tuned cell and backend: **128 processes**.
* Each process decodes all eight fixed JP2s 15 times after three warmups:
  **15,360 timed decode observations**.
* Timing includes decode, actual zune `Image` construction and destruction.
  Input I/O, flattening and reference comparison are outside that region.
* Actual rustc arguments are checked for the executable, zune-image and both
  selected decoder crates. Native final-link commands, executable hashes,
  ELF sections, build time and process/tree RSS are retained.

Python 3.12.16, Pillow 12.0.0 and OpenJPEG 2.5.4 reproduced all sixteen supplied
historical input/reference SHA256 values exactly. Both backends accept 8/8
and independently reproduce all four lossless references. Rust's four lossy
outputs have maximum absolute error 1 against the supplied OpenJPEG references.
Hayro's noisy gray/RGB lossy maxima are 52/54; smooth maxima are 1.
Hayro is not a lossy pixel oracle.

## Timing results

Positive values are elapsed-time reductions, not throughput increases.
Intervals are 95% bootstrap intervals over four matched process-pair blocks;
the eight inputs and fifteen in-process iterations are not independent
population samples. Measurements are exploratory shared-host observations.

| Cell | Rust EPYC reduction % [95%] | Rust N2 reduction % [95%] |
|---|---:|---:|
| CPU only | -3.0435 [-4.1940, -1.8792] | +0.5234 [-0.5951, +1.6294] |
| ThinLTO | -2.9049 [-4.9150, -0.9334] | -0.7201 [-1.7853, +0.7650] |
| CGU1 | -5.8531 [-6.6659, -4.7232] | -5.0073 [-5.8071, -4.3460] |
| Combined | -0.2040 [-0.8695, +0.2947] | **+6.7541 [+6.4603, +7.1601]** |

Rust acceptance, shapes and bytes are unchanged across all five profiles,
both build rounds and generic cross-architecture execution.
Hayro x86 CPU/combined alter its own generic lossy output bytes:
**those timing headlines and comparator ratios are unqualified**, not wins.
Its N2 profiles preserve bytes; approximate reductions are CPU 5.98%,
ThinLTO 3.38%, CGU1 3.47%, combined 5.22%.

Generic matched-configuration Rust/Hayro time geomeans are 5.128x EPYC /
6.337x N2. The handoff's different statistic, median of eight per-fixture
p50 ratios, ranges **4.991-5.739x EPYC / 5.850-6.231x N2** across sixteen
generic process blocks; medians are 5.470x / 6.051x. These are not interchangeable
with geomeans or a repeat of the handoff's original 6.84-6.98x observations.
Build tuning does not explain or remove the remaining backend gap.

## Build, artifact and memory tradeoffs

Ranges contain two cold builds, not confidence intervals.
Native cc time excludes LLVM ThinLTO performed inside rustc.

| Host/cell | Build s | Native cc ms | `.text` bytes | Unstripped ELF bytes | Median decode RSS MiB |
|---|---|---|---:|---:|---:|
| EPYC generic | 33.73-34.40 | 32.71-34.20 | 804582 | 4834224 | 384.40 |
| EPYC CPU | 32.97-33.12 | 33.54-33.94 | 819286 | 4776496 | 384.41 |
| EPYC ThinLTO | 22.22-23.63 | 28.51-31.93 | 792086 | 2856584 | 384.46 |
| EPYC CGU1 | 35.58-37.45 | 27.01-28.33 | 778198 | 4728984 | 384.38 |
| EPYC combined | 25.41-25.55 | 19.46-20.25 | 793558 | 2770064 | 384.38 |
| N2 generic | 36.72-37.20 | 141.73-144.82 | 686264 | 4671280 | 383.96 |
| N2 CPU | 37.62-37.81 | 142.62-150.69 | 698728 | 4649120 | 383.96 |
| N2 ThinLTO | 26.97-27.47 | 80.44-84.91 | 675736 | 2806080 | 383.92 |
| N2 CGU1 | 39.77-39.86 | 109.74-115.84 | 661592 | 4568784 | 383.88 |
| N2 combined | 31.18-31.86 | 66.59-68.10 | 661320 | 2749048 | 383.75 |

ThinLTO shrinks `.text` about 1.55% on either host, not the roughly 40%
unstripped ELF shrink. Prebuilt standard-library debug data is not removed
by consumer debug=0. No stripped-production size is claimed.
Single-process build peaks are approximately 502-507 MiB generic,
606 MiB EPYC / 680 MiB N2 CGU1, and 601-606 MiB combined.
Sampled summed-tree RSS can miss peaks and double-count shared pages.
Decode RSS includes the whole adapter process, input and post-timing work;
generic Hayro medians are 48.17 MiB EPYC / 44.28 MiB N2.
These are not isolated decoder-allocation measurements.

## Additional acceptance and deployment CPUs

[Run 44976887228](https://github.com/microsoft/jpeg2000_rs/actions/runs/44976887228)
executes the unchanged native artifacts against forty immutable public
JP2/J2K/JPH/JPX valid/malformed probes from published source anchor
`4989f9c680beeb7bad4fbfd441a93aa373d2ba4f`. Each input is a separate bounded
process (2 GiB address space, 300 seconds).
This is an explicitly labeled alternative: the handoff's example Hayro corpus
pin `681f6a378dadd84b83ae35849b7071953e724dac` did not resolve. No HEAD substitution
or assertion that this is the same corpus is made.

* N2: all five configurations, both backends and strict/lenient outcomes
  exactly match their own generic baseline, including rejections.
* The acceptance x86 host is **EPYC 7763 / znver3**, not the znver4 build host.
  Generic, ThinLTO and CGU1 execute and match their own generic outcomes.
  CPU-only/combined are explicitly skipped because their deployment CPU
  differs; no portable execution claim is made for those binaries.
* Rust accepts 25/40 strict and 26/40 lenient, with no panic, process failure
  or timeout. Hayro accepts 29/40 strict and 30/40 lenient, with two reported
  panics per mode, unchanged across supported profiles. Matching generic
  outcomes does not mean every probe is valid or accepted.
* Separately, the generic build-host binaries run unchanged on an older local
  EPYC 7763: both backends accept all eight generated inputs, reproduce all
  lossless references, and match their own build-host bytes on all eight,
  including lossy. This is untimed CPU acceptance, not a performance repeat.

## Recommendation and evidence retention

Keep portable defaults. Combined tuning is a **qualified N2-specific
6.75% adapter gain on this cohort**, not a universal default or a claimed gain
for main's newer algorithms. N2 deployment owners may reproduce it with their
own workloads and stripped binaries. No x86 aggregate speed gain qualifies.
Individual CPU/ThinLTO factors do not show a Rust N2 speed win; CGU1 regresses
both hosts. No decoder algorithm, proof boundary or release policy changed.

This study is separate from [the older standalone study](RESULTS.md).
PDFium GN acceptance is separately tracked in [PDFIUM.md](PDFIUM.md);
zune timings do not qualify a PDF renderer.

The maintained [actual evidence index](actual-evidence.json) records source,
hosted ZIP digests and extracted-file inventory receipts. Complete downloaded
native artifacts, fixtures, compiler/link records and raw observations are
retained outside tracked source under:

`/home/sergiog/.copilot/session-state/a689d42c-16cd-4089-bbc6-f20300bb6cc3/files/actual-consumer449-evidence/`

Host-local retention is not an indefinite guarantee; copy this evidence
to an owner-managed store. Hosted downloads expire:

* [EPYC artifact 14734129739](https://github.com/microsoft/jpeg2000_rs/actions/runs/44970463577/artifacts/14734129739):
  2026-12-22 02:09:19 UTC.
* [N2 artifact 14734313912](https://github.com/microsoft/jpeg2000_rs/actions/runs/44970463577/artifacts/14734313912):
  2026-12-22 02:04:59 UTC.
* [x86 acceptance artifact 14735634247](https://github.com/microsoft/jpeg2000_rs/actions/runs/44976887228/artifacts/14735634247):
  2026-12-22 02:37:07 UTC.
* [N2 acceptance artifact 14735903731](https://github.com/microsoft/jpeg2000_rs/actions/runs/44976887228/artifacts/14735903731):
  2026-12-22 02:37:13 UTC.

The download ZIP digests are reported by GitHub; extracted-file SHA256
inventories are separate receipts, not equivalent archive digests.
