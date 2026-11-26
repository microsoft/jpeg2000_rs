# PR492 / PR493 / PR494 exact-source N2 qualification

## Completed original qualification

All four exact sources are built and executed. The original functional,
diagnostic, independent-reference and targeted-test gates pass, and the
complete original timing grid is published. This is not a merge, release,
tradeoff waiver or combined-tree qualification.

All sources have the original2,521 requests (310 images x8 plus41
genuinely lenient PDF renders), actual native build/optimization/source-pair
audits,17 Shim +6 FFI real targeted tests and ten independent controls.
The new f4b Base is executed, not inherited from54ab or a99.

**22,689 actual functional processes /30,252 represented backend outcomes**.
Each candidate shares the fresh immutable Base C++ capture only after actual
binary/input identity checks. Every head preserves Base acceptance/refusals,
geometry/color/channels, output bytes, packed pixel hashes and actual stderr
diagnostics. The original `compare_runs.py` and separate diagnostic gates
have zero differences. All **92 native-consumer tests** and **40 independent
reference decisions** are retained. OpenJPEG is not an infallible oracle.

Source map requested by #490 comment7177635722:

- Base: `f4b2b7b29d38fa31bd74263913462bb67d6e5e4e`
- PR492: `557960d2e36526d82fd0971c3dc5463219880c7b`
- PR493: `590ca79a111f701308665038a83915434d551e80`
- PR494: `2743436c341a679ce62162f3fc3ef72807b98dee`

Original immutable harness:90dd9f013c35739a7d67de869180b62a08bcea23.
Native Neoverse-N2, exact original matching LLVM24, O3/native/CGU1/ThinLTO/
final-linkO3, default features and2GiB data cap are retained. Within every
completed source, C/Rust shim halves match and Shim/FFI core archives are
identical. The original OpenJPEG binary is unchanged.

Actual command hashes and location-only projections are supplied; source
labels retain exact identity while temporary paths are removed. Original XML
outcomes and every status/pixel/refusal remain. The92-test aggregate and per-source XML outcomes record all four sources.

## Completed original performance sweep

All **780 source/case-rounds /2,340 fresh timed processes** completed:
the frozen65 cases x3 rounds x4 sources x3 backends. These are16 synthetic
images,4 HT images,6 extracted images and39 full PDFs per source.
Three warmups and7 image/5 PDF timed repetitions are unchanged. Timing is
serial CPU2, with original rotating source/backend orders. Builds, tests,
functional requests and references finished before timing.

Every timed signature matches its actual functional capture; known embedded
images preflight successfully before PDF timing. No omitted/white image was
credited as a win. Sources, binaries/core archives and all351 input/PDF hashes
were rechecked after execution. No new per-process RSS was measured.

Candidate/Base elapsed-time ratios below use the median of the three
same-round ratios for each case, then geometric means across the indicated
fixed cohort. **Lower is better.** No independent confirmatory confidence
interval or universal/population claim follows from three rounds on a shared
host with a common Base block.

| Candidate | All65 shim / FFI ratios | Four HT images shim / FFI | 39 PDFs shim / FFI | Worst individual median shim / FFI |
|---|---|---|---|---|
| #492 | 0.9902 /0.9901 | **0.9327 /0.9170** | 0.9896 /0.9920 | 1.0408 /1.0425 |
| #493 | 1.0012 /0.9976 | 1.0023 /0.9976 | 1.0001 /0.9961 | 1.0294 /1.0480 |
| #494 | 0.9984 /0.9998 | 1.0086 /1.0125 | 0.9977 /0.9996 | 1.0404 /1.0331 |

**All195 head/case comparisons per Rust integration are supplied. No Rust
per-case median exceeds1.05**, but under-threshold negative observations and
all adverse tails remain reviewable rather than being waived.

### Source-specific value and limits

- **#492:** a demonstrated HT-class improvement in this actual consumer.
  Three noisy HT images improve by about7.2-10.2% through the shim and
  9.5-11.1% through direct FFI. The smooth256 grayscale case is near parity.
  Geometric means across the four HT images imply6.7% less shim time and
  8.3% less FFI time; across all65 workloads the reduction is about1%.
  Selected noisy HT PDF wrappers also improve. This does not complete
  #474's separate narrow-primary/incremental scope, reproduce the earlier
  local17-18% as a consumer-wide gain, establish new RSS savings or erase
  action123/layer/fallback negative evidence.
- **#493:** essentially neutral on the original65-case cohort. The shim
  retains its C++ sYCC conversion; the direct FFI requests the Rust conversion
  for enumerated18. This result does not replace or refute the separately
  qualified28 requested/native-off cases. No material overall benefit,
  additional MCT gain or OpenJPEG-conversion-equivalence claim is made.
  The worst FFI median is1.04799 on the1024-gray smooth-lossy PDF wrapper.
- **#494:** essentially neutral on this original cohort, not the separately
  measured high-tile-count scaling targets. The frozen corpus is not
  substituted with those targets to obtain a win. The1024-gray HT shim
  median is1.03993 and the1024-gray smooth-lossless wrapper is1.04044:
  these negative controls are retained. Earlier256-interleaved and ROI
  negative/tail findings remain separately valid; no overall65-case or
  universal index/RSS improvement is claimed.

Coordinator retention/adoption is still distinct from this completed gate.
These independently tested changes are not a qualified combined stack.

### Absolute HT medians and paired ratios for #492

The original Source/Case/Backend tables include every absolute p50/p90;
selected image medians in milliseconds are:

| HT image | Shim Base -> #492 | Same-round median ratio | FFI Base -> #492 | Same-round median ratio |
|---|---|---|---|---|
|1024 gray noise|130.870 ->120.495|0.927699|133.286 ->120.580|0.904857|
|1024 RGB noise|403.254 ->361.654|0.897783|398.142 ->359.945|0.895931|
|256 gray smooth|3.064 ->3.039|0.995190|3.086 ->3.026|0.980585|
|256 RGB noise|23.822 ->21.786|0.913178|23.296 ->20.654|0.889375|

The ratio of displayed median times need not equal the median of paired
same-round ratios. Raw repeats, p90 and order are unchanged and supplied.

## Every adverse tail and unchanged-C++ control

There are **16 Rust p90 median-ratio rows above1.05**:
3 for #492,5 for #493 and8 for #494. All are retained below. There are also
14 such p90 rows for the unchanged C++ control (5/6/3 by head).
Full details and all three ratios are in `performance-summary.json`.

| PR | Backend | Workload | Same-round p90 ratio |
|---|---|---|---:|
|492|shim|synthetic/256-RGB-smooth-lossless.jp2|1.057230|
|492|shim|resources/pixel/jpxdecode_with_mismatch_colorspace.pdf|1.077346|
|492|shim|resources/pixel/jpxdecode_without_smaskindata.pdf|1.248000|
|493|shim|embedded/8ac3ec64-255.jp2|1.226424|
|493|shim|resources/pixel/jpxdecode_with_mismatch_colorspace.pdf|1.238486|
|493|shim|resources/pixel/jpxdecode_without_smaskindata.pdf|1.103880|
|493|ffi|embedded/8ac3ec64-256.jp2|1.234985|
|493|ffi|resources/pixel/jpxdecode_smask_in_data_2.pdf|1.073874|
|494|shim|embedded/8ac3ec64-255.jp2|1.207108|
|494|shim|embedded/8ac3ec64-256.jp2|1.081096|
|494|shim|resources/pixel/jpxdecode.pdf|1.127822|
|494|shim|resources/pixel/jpxdecode_with_mismatch_colorspace.pdf|1.137205|
|494|shim|resources/pixel/jpxdecode_without_smaskindata.pdf|1.104817|
|494|ffi|embedded/8ac3ec64-256.jp2|1.075392|
|494|ffi|resources/pixel/jpxdecode_smask_in_data_2.pdf|1.530426|
|494|ffi|resources/pixel/jpxdecode_with_mismatch_colorspace.pdf|1.067541|

The identical OpenJPEG executable also has **two median ratios above1.05**
in the PR493 block: `embedded/8ac3ec64-255.jp2`1.060340 and
`jpxdecode_indexed2.pdf`1.054320. Its worst observed p90 ratio is2.408857.
All C++ rows remain; identical code demonstrates variability, not the cause
of any Rust tail or permission to delete it.

Seven/five samples make per-process p90 near/max-sample, not a population
tail estimate. No causal explanation, rerun-until-pass, artificial alignment,
trimmed observation, universal tail win or tradeoff approval is claimed.
`performance-analysis.json` additionally retains **all996 individual-round
above-parity median/p90 observations**, including below5% negatives and C++
controls, so reporting thresholded medians does not hide adverse rounds.

## Complete files and provenance

`receipt.json` addresses all exported files. Each source directory contains
the build/source/ABI audit, full original matrix/gate, real test XML,
reference decisions, original comparison gate and separate diagnostic report.
`native-tests.json` preserves the92-test batch summary.

`performance.json` contains all780 source/case-rounds; `per-case.tsv` and
`performance-summary.json` contain every per-case absolute median/p90 and
paired ratio. `performance-analysis.json` supplies fixed-cohort/group
geometric means and every above-parity round, not a selection of wins.
Actual command-byte hashes, location-only projections and Rust response
flags are in `actual-command-projections.json.gz`.

Original input IDs/bytes, generated encodings, decoder limits, feature
profile, compiler revisions, packing and arithmetic are unchanged. This
study adds no native/CAPI/package/source-proof or owner waiver. Prior
independent native findings remain bound to their original protocols.

No decoder, corpus, arithmetic, limits, policy, release/backport, owner
tradeoff, merge or adoption was changed. Later combined adoption needs a
separate exact-tree qualification. Historical receipts and negative evidence
are not relabeled or erased.
