# Native final-consumer results for #449

This document preserves the **earlier standalone** study. The completed
[actual zune adapter study](ZUNE_RESULTS.md) is separate: its qualified combined
N2 gain is 6.75%, not the 2.78% standalone result below. PDFium qualification
uses [its own GN study](PDFIUM.md). No observations are pooled.

## Scope and evidence

[PR #450](https://github.com/microsoft/jpeg2000_rs/pull/450), manual
[run 44825727854](https://github.com/microsoft/jpeg2000_rs/actions/runs/44825727854),
measurement commit `c96b7d1cc99b92136d97fdbe7d5d3ff50a3dcc7b`: **60 fresh-target
builds, 4,608 new-process observations; all 11 jobs succeeded**.

Observed native hosts: 4-vCPU **AMD EPYC 9V74** (`ubuntu-latest`) and 4-vCPU
**Neoverse-N2** (`ubuntu-24.04-arm`), not emulation or cross-build timings.
Rust 1.93.1 and the consumer lockfile were pinned. Current control
`97d5162b3f43fb14942c46bbea73752d26fb24b4` and published 0.2.2 have identical
runtime/spec/proof sources. All 380 files and the published package hash were
rechecked unchanged; hashes are in [evidence.json](evidence.json).

The shared manifest remains
`5c33c9699031796f293e4cb5357c56748367793cbd21c59e7ddaba219069c954`.
Eight frozen self-authored JP2s, exact extracted raw J2Ks and eight tracked
probes comprise the 24 inputs; four integer-generated PNM sources are hashed.
No private/PDF inputs were added. See [README.md](README.md) for reproduction,
flags, API/timing boundaries, ordering, memory definitions and uncertainty.

## Decode findings

Positive values mean **decode-time reduction**, not throughput improvement.
Current-main intervals are 95% bootstrap intervals over four matched pair
blocks. The 16 generated JP2/J2K inputs are correlated copies of eight cases,
not independent population samples. All raw observations were retained.

| Host | Configuration | Current-main reduction, % [95% interval] | Published 0.2.2 reduction, % |
|---|---|---:|---:|
| EPYC | CPU only | −2.35 [−2.77, −2.02] | −1.98 |
| EPYC | ThinLTO only | −0.43 [−0.73, −0.05] | −0.12 |
| EPYC | CGU1 only | −3.24 [−3.69, −2.78] | −2.42 |
| EPYC | Combined | −0.81 [−0.93, −0.67] | +0.03 |
| N2 | CPU only | −0.20 [−0.54, +0.21] | +0.10 |
| N2 | ThinLTO only | −0.03 [−0.24, +0.21] | −0.32 |
| N2 | CGU1 only | −2.66 [−2.98, −2.33] | −2.66 |
| N2 | Combined | +2.78 [+2.30, +3.26] | +2.64 |

CPU means `target-cpu=native`; combined adds ThinLTO and CGU1. Individual
factors were otherwise isolated. The earlier complete ARM repeat observed
+2.70% combined reduction; it is retained separately, not pooled.

Our current/published controls preserve exact acceptance, dimensions and
sample fingerprints across every configuration, repeated observation and
native host. Generated lossless outputs independently recover source hashes.
Hayro 0.3.5 scalar uses only `std`, with default features disabled. On x86,
CPU/combined settings change all eight lossy-input fingerprints: those
headline comparisons are **null/unqualified**, with every variant retained.
Hayro lossy samples also differ across architectures and from ours; it is
**not a pixel oracle**, and no lossy numerical adjudication is claimed.
Generic current/Hayro geomean time ratios are **5.482× EPYC / 6.244× N2**,
not backend-paired or adapter-identical zune-image measurements.

## Build, size and memory interpretation

Current-main generic → ThinLTO → combined observations:

| Host | Build wall ranges, s | Final executable native-cc median, ms | Unstripped ELF, bytes |
|---|---|---|---|
| EPYC | 11.17–11.43 → 11.51–11.69 → 14.22–14.61 | 26.4 → 23.9 → 18.9 | 4,589,624 → 2,624,456 → 2,544,408 |
| N2 | 16.14–16.19 → 16.32–16.40 → 20.24–20.25 | 115.0 → 75.7 → 63.8 | 4,547,352 → 2,612,064 → 2,561,440 |

Two reversed build rounds give ranges, not confidence intervals. Native-cc
time excludes LLVM ThinLTO inside rustc; all compiler/link invocations remain
available. The roughly 43% ThinLTO **unstripped file-size** reduction is not
a stripped-production/code-size claim: prebuilt standard-library debug data
remains with consumer debug=0. `.text` shrinks only **1.95% EPYC / 2.19% N2**.

Across settings, observed current-main build peaks were 515–545 MiB for one
process / 612–668 MiB sampled summed-tree RSS on EPYC, and 514–543 / 619–676
MiB on N2. Tree sampling can miss peaks and double-count shared pages.
Decode-process peaks were 353.9 / 353.4 MiB; generic Hayro peaks were 38.0 /
37.5 MiB. These include startup/input/post-timing fingerprinting and different
API footprints, **not** isolated or adapter-identical allocation peaks.
Per-input, backend, configuration and round detail remains in external data.

## Standalone recommendation and historical handoff

Retain portable defaults. CPU tuning and CGU1 are not universal improvements;
the small combined ARM gain does not improve EPYC or explain the large gap.
ThinLTO can be tested for modest code-size benefits on the actual stripped
consumer artifact, not assumed to produce a decode-speed gain.

At the time of this standalone study, the shared zune workspace existed at `/workspace/zune-image/zune-image`, HEAD
`13edc8d07f1572f149f83c59cf861211042c9874`. Its release profile declares debug=2;
dist inherits release with ThinLTO. No workspace Cargo manifest has a JPEG
2000/Hayro/JP2/J2K dependency/feature and benchmarks have no J2K entry.
The missing item is **actual J2K integration/comparison harness**, not the
workspace. See [root-profile propagation](README.md#historical-shared-zune-workspace-inspection).
Shared dirty changes were not edited/copied/published; no zune build was run.
`/workspace/pdfium-dev` was absent. Actual integration was therefore a
remaining qualification item, subsequently unblocked by the public handoff.
No decoder/default/release-policy change or merge is proposed.

The [subsequent consumer handoff](https://github.com/microsoft/jpeg2000_rs/issues/449#issuecomment-7071726628)
now unblocks a clean, pinned zune integration without that shared workspace.
Its exact sixteen historical input/reference hashes were reproduced with
Python 3.12, Pillow 12.0.0 and OpenJPEG 2.5.4. Both locked generic consumers
accept all eight inputs on native x86-64 and reproduce all four lossless source
references; supplied adapter controls pass against published 0.2.2. This is
smoke evidence, not a profile-speed claim. The completed optional native
integration matrix and expanded acceptance are documented in
[ZUNE_RESULTS.md](ZUNE_RESULTS.md); the standalone measurements above are not
substituted for them. The separate PDFium GN study still requires its own
pixel/error qualification.

## Raw-data access and retention

Generated reports are **outside tracked source**, following
[RELEASING.md](../../RELEASING.md#source-publication). The maintained
[evidence index](evidence.json) records exact hashes, locations and run links.
All 50,146 preserved files (1,014,976,603 bytes), including complete downloaded
artifacts/executables, inputs, logs, failed attempts, raw archives and long
summaries, were byte-verified against their originals at:

`/home/sergiog/.copilot/session-state/a689d42c-16cd-4089-bbc6-f20300bb6cc3/files/consumer-tuning-449-evidence/`

`SHA256SUMS` and `preservation-manifest.json` index that local snapshot.
`generated-results/` contains all former reports; `target-evidence/` contains
the full raw evidence. This is host-local, not a public download or an
indefinite-retention guarantee; owners should copy it to their evidence store.

Full hosted artifacts also contain executables, but expire after **30 days**:
[EPYC artifact 14674548585](https://github.com/microsoft/jpeg2000_rs/actions/runs/44825727854/artifacts/14674548585)
expires **2026-12-20 22:21:03 UTC**;
[N2 artifact 14674977659](https://github.com/microsoft/jpeg2000_rs/actions/runs/44825727854/artifacts/14674977659)
expires **2026-12-20 22:23:24 UTC**. Run links do not guarantee artifact
availability after expiry. Earlier attempt data is preserved locally; its
incomplete qualification and invalid earlier summed-tree RSS remain labeled.
Removal from the current tree is an ordinary follow-up commit, **not** erasure
from prior Git history; no history rewrite or force-push was performed.
