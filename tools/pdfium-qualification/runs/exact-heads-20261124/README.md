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

## Performance status

The original65-workload performance selection is executing for all five
sources: three rounds, three warmups,7 image/5 PDF timed repetitions, CPU2,
with rotating source and backend order and actual image preflight checks.
Builds and functional tests finished before timing began. Every timed
signature must equal the corresponding actual functional capture.

Performance results are **pending** in this checkpoint. The functional pass
alone is not retention/merge approval or disposition of documented tail
tradeoffs. Completed receipts will retain every adverse measurement.

## Files and reproduction

Each label directory contains the actual audit, complete functional outcome
matrix, base/head difference gate and oracle decisions. `sources.json` binds
labels to immutable commits. `targeted-tests.json` records all ten test runs;
`receipt.json` addresses all exported files. Machine-local paths and temporary
pixel locations are removed, not logical outcomes or refusal decisions.

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
