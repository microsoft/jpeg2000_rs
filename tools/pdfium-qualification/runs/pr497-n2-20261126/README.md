# PR497 exact-source N2/LLVM24 PDFium qualification (`Base 043b772` vs `PR497 d965df0`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `043b772723954bc4c8fa8ac741f46f26ca183f59` (merged `main` including #496)
  - `PR497`: `d965df06d6fbfdb0d9aa652b124d634885177318` (draft PR #497, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `ae94898eed2920076ca950092f8b6c71a8f1d9e8`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR497` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9955** | **0.9913** | 0.9997 | **0.9926** | 0.9972 | `wrapped/synthetic-1024-L-smooth-lossy.pdf` (`1.0263`) | **0** | 3 |
| **Direct FFI** | **0.9953** | **0.9927** | 0.9963 | **0.9931** | 0.9967 | `resources/pixel/jpxdecode.pdf` (`1.0272`) | **0** | 3 |
| **OpenJPEG2 (unchanged control)** | 0.9985 | 1.0007 | 0.9971 | 0.9947 | 0.9983 | `resources/pixel/bug_1012369.pdf` (`1.0616`) | 1 | 5 |

### Lossy Synthetic (8 Images) and Key Embedded/PDF Workloads

| Workload | Shim `PR497/Base` (p50 ms) | FFI `PR497/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `synthetic/256-L-noise-lossy.jp2` | **0.9679** (`7.331 -> 7.088`) | **0.9716** (`7.278 -> 7.071`) | 0.9924 |
| `synthetic/1024-RGB-smooth-lossy.jp2` | **0.9706** (`246.422 -> 239.461`) | **0.9721** (`244.564 -> 237.750`) | 1.0070 |
| `synthetic/256-RGB-noise-lossy.jp2` | **0.9706** (`21.171 -> 20.548`) | **0.9895** (`20.796 -> 20.578`) | 1.0093 |
| `synthetic/1024-RGB-noise-lossy.jp2` | **0.9715** (`370.780 -> 361.999`) | **0.9746** (`368.841 -> 359.472`) | 0.9958 |
| `synthetic/1024-L-noise-lossy.jp2` | **0.9819** (`123.236 -> 120.891`) | **0.9826** (`122.453 -> 119.672`) | 1.0008 |
| `synthetic/1024-L-smooth-lossy.jp2` | **0.9828** (`65.012 -> 63.593`) | **0.9929** (`64.925 -> 63.383`) | 1.0015 |
| `synthetic/256-RGB-smooth-lossy.jp2` | 0.9935 (`11.097 -> 11.025`) | 0.9916 (`11.043 -> 10.951`) | 0.9978 |
| `synthetic/256-L-smooth-lossy.jp2` | 0.9951 (`3.902 -> 3.873`) | 0.9940 (`3.909 -> 3.873`) | 0.9909 |
| `embedded/77e45cf2-264.jp2` | **0.9820** (`478.300 -> 469.900`) | **0.9739** (`476.633 -> 464.198`) | 0.9954 |
| `embedded/53ccd6a1-271.jp2` | 0.9929 (`1252.010 -> 1243.082`) | 0.9929 (`1226.918 -> 1217.246`) | 0.9969 |
| `corpus/fx/action/123.pdf` | **0.9849** (`504.595 -> 497.543`) | **0.9820** (`504.513 -> 499.510`) | 0.9874 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0`
- **Unchanged OpenJPEG2 medians > 1.05:** `1` (`resources/pixel/bug_1012369.pdf` `1.0616`)
- **Rust p90 > 1.05 (6 rows — 3 Shim, 3 FFI; all `< 1.1 ms` workloads):**
  - Shim `resources/pixel/jpxdecode_smask_in_data_2.pdf`: p50 `0.9805`, p90 ratio `1.3230` (rounds `0.615/1.331/1.323`, `0.449 -> 0.562 ms`)
  - Shim `embedded/8ac3ec64-255.jp2`: p50 `0.9847`, p90 ratio `1.1721` (rounds `1.006/1.172/1.245`, `0.872 -> 0.989 ms`)
  - Shim `resources/pixel/jpxdecode_indexed2.pdf`: p50 `1.0137`, p90 ratio `1.0637` (rounds `1.018/1.146/1.064`, `0.918 -> 1.052 ms`)
  - FFI `resources/pixel/jpxdecode.pdf`: p50 `1.0272`, p90 ratio `1.0691` (rounds `1.069/1.261/0.907`, `0.962 -> 1.028 ms`)
  - FFI `embedded/98cfa38a-280.jp2`: p50 `1.0026`, p90 ratio `1.0643` (rounds `1.029/1.284/1.064`, `0.894 -> 1.104 ms`)
  - FFI `resources/pixel/jpxdecode_smask_in_data_2.pdf`: p50 `0.9983`, p90 ratio `1.0584` (rounds `1.058/0.633/1.374`, `0.448 -> 0.441 ms`)
- **Unchanged OpenJPEG2 p90 > 1.05 (5 rows):** `synthetic/256-RGB-smooth-lossless.jp2` (`1.2264`), `resources/pixel/bug_1012369.pdf` (`1.1524`), `resources/pixel/jpxdecode_without_bitspercomponent.pdf` (`1.1508`), `resources/pixel/jpxdecode_indexed2.pdf` (`1.0779`), `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.0713`).

No merge, release, backport, runtime change, or #474 closure was performed.
