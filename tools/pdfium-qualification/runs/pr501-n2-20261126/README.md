# PR501 exact-source N2/LLVM24 PDFium qualification (`Base c7b8473` vs `PR501 4e78ee6`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `c7b8473e7aedddba23989753679627c361a3a34a` (merged `main` including #500)
  - `PR501`: `4e78ee66b6a3541ae9e875d1eb8dca00a70813e4` (draft PR #501, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `00028b47df05698eddecff62b091408219d0df4f`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR501` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9740** | **0.9530** | 0.9990 | **0.9884** | **0.9780** | `resources/pixel/jpxdecode_without_smaskindata.pdf` (`1.0280`) | **0** | 4 |
| **Direct FFI** | **0.9736** | **0.9519** | **0.9936** | 1.0023 | **0.9763** | `wrapped/synthetic-1024-L-smooth-lossless.pdf` (`1.0353`) | **0** | 3 |
| **OpenJPEG2 (unchanged control)** | 0.9997 | 1.0007 | 0.9967 | 0.9984 | 0.9998 | `resources/bug_1396264.pdf` (`1.0320`) | 0 | 4 |

### Selected Legacy Tier-1 LUT & Interior-Mark Wins

| Workload | Shim `PR501/Base` (p50 ms) | FFI `PR501/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `synthetic/256-RGB-noise-lossless.jp2` | **0.8668** (`51.908 -> 45.005`) | **0.8660** (`51.803 -> 44.868`) | 1.0009 |
| `synthetic/256-L-noise-lossless.jp2` | **0.8667** (`17.495 -> 15.163`) | **0.8683** (`17.464 -> 15.210`) | 0.9995 |
| `wrapped/synthetic-256-RGB-noise-lossless.pdf` | **0.8667** (`52.696 -> 45.679`) | **0.8682** (`52.464 -> 45.498`) | 0.9991 |
| `synthetic/1024-L-noise-lossless.jp2` | **0.8704** (`283.364 -> 246.865`) | **0.8719** (`283.051 -> 245.499`) | 1.0007 |
| `synthetic/1024-RGB-noise-lossless.jp2` | **0.8735** (`848.455 -> 740.895`) | **0.8731** (`847.868 -> 740.310`) | 1.0004 |
| `wrapped/synthetic-1024-RGB-noise-lossless.pdf` | **0.8731** (`855.483 -> 747.788`) | **0.8765** (`854.422 -> 748.723`) | 1.0025 |
| `wrapped/synthetic-1024-L-noise-lossless.pdf` | **0.8753** (`288.123 -> 253.131`) | **0.8743** (`288.172 -> 251.938`) | 1.0001 |
| `resources/pixel/bug_1469.pdf` | **0.9478** (`5.009 -> 4.746`) | **0.9454** (`4.990 -> 4.686`) | 1.0083 |
| `synthetic/1024-L-noise-lossy.jp2` | **0.9626** (`102.763 -> 98.104`) | **0.9658** (`103.192 -> 98.480`) | 1.0027 |
| `synthetic/256-RGB-noise-lossy.jp2` | **0.9626** (`16.936 -> 16.303`) | **0.9616** (`16.851 -> 16.177`) | 1.0019 |
| `embedded/77e45cf2-264.jp2` | **0.9914** (`396.423 -> 389.844`) | **0.9914** (`392.909 -> 387.635`) | 1.0003 |
| `corpus/fx/action/123.pdf` | **0.9944** (`410.666 -> 404.598`) | **0.9869** (`412.552 -> 406.073`) | 1.0063 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0` (Shim max `1.0280`, FFI max `1.0353`)
- **Unchanged OpenJPEG2 medians > 1.05:** `0`
- **Rust Shim p90 > 1.05 (4 rows, all `< 1.04 ms`):**
  - Shim `resources/pixel/jpxdecode_indexed2.pdf`: p50 `0.9956`, p90 ratio `1.2161` (rounds `1.232/1.216/1.167`, `0.854 -> 1.038 ms`)
  - Shim `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf`: p50 `0.9954`, p90 ratio `1.1534` (rounds `0.822/1.347/1.153`, `0.799 -> 0.922 ms`)
  - Shim `embedded/8ac3ec64-256.jp2`: p50 `0.9882`, p90 ratio `1.0899` (rounds `1.137/1.090/0.981`, `0.823 -> 0.895 ms`)
  - Shim `resources/pixel/jpxdecode_without_smaskindata.pdf`: p50 `1.0280`, p90 ratio `1.0678` (rounds `1.068/1.322/1.004`, `0.691 -> 0.791 ms`)
- **Rust FFI p90 > 1.05 (3 rows, all `< 1.07 ms`):**
  - FFI `embedded/98cfa38a-280.jp2`: p50 `0.9936`, p90 ratio `1.1191` (rounds `1.119/1.005/1.208`, `0.761 -> 0.911 ms`)
  - FFI `embedded/8ac3ec64-255.jp2`: p50 `1.0203`, p90 ratio `1.0624` (rounds `1.029/1.124/1.062`, `0.792 -> 0.829 ms`)
  - FFI `resources/pixel/jpxdecode_without_colorspace.pdf`: p50 `0.9886`, p90 ratio `1.0561` (rounds `1.196/0.911/1.056`, `0.921 -> 1.068 ms`)
- **Unchanged OpenJPEG2 p90 > 1.05 (4 rows):** `resources/pixel/jpxdecode_smask_in_data_2.pdf` (`1.5159`), `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.2916`), `synthetic/256-L-noise-lossy.jp2` (`1.1986`), `wrapped/synthetic-256-L-smooth-lossy.pdf` (`1.1929`).

No merge, release, backport, runtime change, or #474 closure was performed.
