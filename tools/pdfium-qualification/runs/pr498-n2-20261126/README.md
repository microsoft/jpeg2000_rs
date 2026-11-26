# PR498 exact-source N2/LLVM24 PDFium qualification (`Base d727599` vs `PR498 5040d77`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `d7275991ce537a067f631d2d94946a98b48704f1` (merged `main` including #497)
  - `PR498`: `5040d775cb19cc5b3782c1db45fe49d18e037e5d` (draft PR #498, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `54655f938987044a566b6eb0f929670a79fa6613`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR498` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9650** | **0.9431** | 1.0001 | **0.9773** | **0.9687** | `resources/pixel/bug_1012369.pdf` (`1.0373`) | **0** | **0** |
| **Direct FFI** | **0.9649** | **0.9450** | 0.9962 | **0.9788** | **0.9679** | `resources/pixel/jpxdecode_smask_in_data_2.pdf` (`1.0321`) | **0** | 3 |
| **OpenJPEG2 (unchanged control)** | 1.0041 | 1.0005 | 1.0014 | 0.9938 | 1.0074 | `resources/pixel/jpxdecode_indexed.pdf` (`1.0647`) | 2 | 8 |

### Selected Legacy Synthetic, Embedded, and Real PDF Wins

| Workload | Shim `PR498/Base` (p50 ms) | FFI `PR498/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `resources/pixel/bug_1469.pdf` | **0.7700** (`7.495 -> 5.770`) | **0.7746** (`7.398 -> 5.729`) | 0.9804 |
| `synthetic/1024-RGB-smooth-lossless.jp2` | **0.9027** (`183.369 -> 165.612`) | **0.9035** (`182.026 -> 163.753`) | 0.9937 |
| `synthetic/256-L-noise-lossy.jp2` | **0.9114** (`7.107 -> 6.477`) | **0.9157** (`7.043 -> 6.447`) | 1.0035 |
| `synthetic/256-L-noise-lossless.jp2` | **0.9129** (`20.570 -> 18.778`) | **0.9158** (`20.500 -> 18.803`) | 0.9994 |
| `synthetic/1024-L-noise-lossless.jp2` | **0.9141** (`332.974 -> 304.650`) | **0.9182** (`331.495 -> 304.371`) | 0.9996 |
| `synthetic/256-RGB-noise-lossless.jp2` | **0.9146** (`61.007 -> 55.875`) | **0.9156** (`61.044 -> 55.788`) | 0.9999 |
| `synthetic/1024-RGB-noise-lossless.jp2` | **0.9160** (`999.005 -> 912.513`) | **0.9147** (`997.150 -> 911.842`) | 0.9997 |
| `synthetic/256-RGB-noise-lossy.jp2` | **0.9167** (`20.109 -> 18.429`) | **0.9133** (`20.047 -> 18.325`) | 1.0059 |
| `resources/pixel/jpxdecode_indexed.pdf` | **0.9461** (`1.105 -> 1.041`) | **0.9447** (`1.102 -> 1.067`) | 1.0647 |
| `embedded/77e45cf2-264.jp2` | **0.9561** (`463.753 -> 444.080`) | **0.9501** (`464.798 -> 439.408`) | 1.0022 |
| `corpus/fx/action/123.pdf` | **0.9572** (`486.767 -> 467.389`) | **0.9575** (`489.870 -> 470.333`) | 1.0134 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0`
- **Rust Shim p90 > 1.05:** `0`
- **Rust FFI p90 > 1.05 (3 rows, all `< 1.13 ms` workloads):**
  - FFI `resources/pixel/jpxdecode.pdf`: p50 `0.9958`, p90 ratio `1.1064` (rounds `1.106/0.908/1.171`, `1.018 -> 1.126 ms`)
  - FFI `resources/pixel/jpxdecode_indexed2.pdf`: p50 `0.9821`, p90 ratio `1.0873` (rounds `1.087/0.830/1.209`, `0.932 -> 1.014 ms`)
  - FFI `resources/pixel/jpxdecode_without_smaskindata.pdf`: p50 `0.9807`, p90 ratio `1.0552` (rounds `1.469/1.055/0.781`, `0.637 -> 0.673 ms`)
- **Unchanged OpenJPEG2 medians > 1.05 (2 rows):** `resources/pixel/jpxdecode_indexed.pdf` (`1.0647`), `resources/bug_1396264.pdf` (`1.0644`).
- **Unchanged OpenJPEG2 p90 > 1.05 (8 rows):** `embedded/8ac3ec64-255.jp2` (`1.7294`), `resources/bug_1396264.pdf` (`1.2528`), `resources/pixel/jpxdecode_without_smaskindata.pdf` (`1.2284`), `synthetic/256-L-noise-lossy.jp2` (`1.2066`), `synthetic/256-L-smooth-lossy.jp2` (`1.1076`), `wrapped/ht-256-L-smooth-lossless.pdf` (`1.0862`), `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.0818`), `resources/pixel/jpxdecode_indexed.pdf` (`1.0551`).

No merge, release, backport, runtime change, or #474 closure was performed.
