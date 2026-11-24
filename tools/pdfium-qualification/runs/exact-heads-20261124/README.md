# Exact-head native N2 consumer qualification

The original evaluator host has accepted the handoff from #490. This is
actual new execution, not historical replay, an x86 substitute or a new corpus.

| Label | Exact source |
|---|---|
| Common base | `54abff44a778b6c210d580770286a531370550b6` |
| #485 | `09962930ea9982d253f91b605c5f311de4f7a9be` |
| #486 | `5d548158a6be8d20e4ec0aff946724453701e3db` |
| #488 | `09b5006df6c4048c0676310d7a56db90ad510a6a` |
| #489 | `0dcd53fc6317747c5fd837b6264ff2b4ee276be1` |

## Completed functional gate

All five sources have actually built shim and direct-FFI consumers on native
Neoverse-N2 ARM64 with the original matching LLVM24 toolchains and prepared
PDFium. Every source passes the full original **2,521-configuration** gate:
**310 images x8 requests plus41 genuinely lenient full-PDF renders**.

All four exact heads preserve the common-base status, geometry, channel/color
metadata and packed pixel signatures on every configuration. No difference
was silently waived. All115 targeted actual PDFium tests pass.
All ten independent-reference controls were executed for every source, with
their decisions retained, including cases where OpenJPEG is not the oracle.

The original OpenJPEG binary remains
`b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.
A fresh immutable common-base C++ capture is shared by the four heads only
after binary/input identity checks. There are **27,731 actual functional
processes** and **37,815 represented backend outcomes**, not37,815 separate
processes. Functional heads ran on separate N2 cores; timing is not parallel.

The audits verify actual O3/native/ThinLTO/NDEBUG C/C++ and opt3/native/one-CGU
Rust with linker-plugin LTO and final --lto-O3. They bind each C shim source to
the exact same checkout as its Rust half; #488 uses its ABI-v3 pair. Within
every revision, shim and FFI core archives are byte-identical.

This is the original default-feature consumer profile. Feature-unified
cooperative-deadline/native-CAPI controls remain distinct requirements; no
claim is made that this consumer substitutes for those dedicated controls.

## Completed performance study

The original65-workload selection completed for all five sources:
**975 source/case-rounds / 2,925 fresh timed processes**. Each process uses
three warmups and7 image/5 PDF timed repetitions. Timing ran serially on
CPU2 with rotating source/backend order, after all builds and functional
tests finished. Every timed signature matches its actual functional capture;
known embedded images preflight successfully before PDF timing.

The complete grid contains16 synthetic images,4 HT images,6 extracted
images and39 PDFs per source. No case, repetition or adverse observation was
dropped, replaced or retimed. Sources, binaries and all351 input/PDF hashes
were rechecked after execution.

Ratios below are candidate/base elapsed time: **lower is better**.
Per-case ratios are medians of the three same-round ratios. Overall ratios
are their geometric means across the frozen65 workloads, not a document
population estimate.

| PR | Overall shim / FFI ratio | Worst per-case shim / FFI median ratio | p90 ratios above1.05, shim / FFI |
|---|---|---|---|
| #485 | 0.9892 / 0.9928 | 1.0125 / 1.0474 | 2 / 3 |
| #486 | 1.0010 / 1.0007 | 1.0308 / 1.0317 | 4 / 1 |
| #488 | 0.9903 / 0.9991 | 1.0345 / 1.0201 | 2 / 3 |
| #489 | 0.9497 / 0.9500 | 1.0493 / 1.0059 | 2 / 0 |

**No Rust-backed per-case median ratio exceeds1.05** across the520 head/case/
backend comparisons. This is a bounded observed result, not a universal
regression-free guarantee or automatic retention decision.

Source-specific observations:

- **#485:** the four HT image ratios have geometric means0.9281 shim /
  0.9386 FFI. Three noisy HT images improve, while the smooth256 grayscale
  image is near parity. This does not close the separately documented HT
  coverage gaps or the x86 irreversible tradeoff.
- **#486:** the original consumer cohort is essentially neutral overall.
  `bug_1258634.pdf` ratios are0.9919 shim /0.9895 FFI; the stronger authored
  mixed-precision native palette findings are not reproduced or invalidated
  by this packed8-bit consumer cohort.
- **#488:** the shim improves selected tiny PDF pages, e.g.
  `jpxdecode_smask_in_data_2.pdf` ratio0.7922. FFI is approximately neutral.
  The feature-unified deadline/native-CAPI gate and prior header/refusal
  tradeoffs remain separate; this is the default-feature PDFium profile.
- **#489:** the frozen65-case geometric means are about0.95 for both Rust
  integrations, but individual gains differ. The large sparse
  `bug_453723.pdf` is near parity:0.9953 shim /0.9941 FFI. This run does not
  establish the earlier large-sparse speedup or an RSS saving.

### Adverse tails and unchanged-C++ controls

All **17 Rust p90 ratios above1.05** remain explicitly listed in
`performance-summary.json` under `adverse_p90_over_5_percent`; none is
waived. Worst observed ratios are:

| PR | Shim p90 ratio and workload | FFI p90 ratio and workload |
|---|---|---|
| #485 | 1.1003, `jpxdecode.pdf` | 1.2526, `jpxdecode_smask_in_data_2.pdf` |
| #486 | 1.3711, `jpxdecode_smask_in_data_2.pdf` | 1.1837, `jpxdecode_without_bitspercomponent.pdf` |
| #488 | 1.1090, `jpxdecode_without_bitspercomponent.pdf` | 1.2237, `jpxdecode_without_smaskindata.pdf` |
| #489 | 1.1570, `jpxdecode.pdf` | none above1.05; worst1.0341, `jpxdecode_smask_in_data_2.pdf` |

The same unchanged OpenJPEG executable was independently timed within every
source block. It has **six median and25 p90 ratios above1.05** across blocks
(maximum median1.0988, maximum p90 ratio2.2618). All are retained, including
the C++ control review list. This demonstrates variability despite identical
code; it does not identify the cause of any particular Rust observation or
justify deleting it.

Only three rounds were run on a shared N2 host. Each head shares the same
base block, so comparisons are correlated/descriptive, not independent
confirmatory confidence intervals. Seven/five samples make per-process p90
near/max-sample, not a reliable population tail estimate. Full raw p50/p90,
source/backend order and every per-round ratio are supplied. No new
per-process RSS measurement or causal hardware-counter attribution is
claimed. Earlier PR-specific negative observations remain separately valid.

The execution/asset-availability blocker is resolved. Owner review of these
tails and previously documented tradeoffs, required source/proof/feature
checks and merge authority are not supplied by this receipt.

## Files and reproduction

Each label directory contains the actual audit, complete functional outcome
matrix, base/head difference gate and oracle decisions. `sources.json` binds
labels to immutable commits. `targeted-tests.json` records all ten test runs;
`receipt.json` addresses all exported files. Machine-local paths and temporary
pixel locations are removed, not logical outcomes or refusal decisions.
`performance.json` retains all975 source/case-rounds.
`performance-summary.json` and `per-case.tsv` expose every median and p90
comparison, including adverse Rust rows and unchanged-C++ controls.

The executable multi-head protocol is `qualify_heads.py` one directory level
above `runs/`. Its local source configuration maps each label to
`{"sha": "...", "path": "/absolute/clean/source"}`. Configure with
`configure.py --prefix Base` or the matching PR prefix to keep per-source
outputs separate; use `audit.py --prefix ...` for every revision. Run the
common-base functional capture first, then each head. Only after all
functional work finishes run references and performance.

No source implementation, dependency, solver/resource policy, private ABI
mixing, optional feature or decoder limit was changed to obtain this gate.
No merge, release, backport or owner tradeoff approval is implied.
