# PR502 exact-source N2/LLVM24 PDFium qualification (`Base fe0d4eb` vs `PR502 357ab64`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `fe0d4eb3fd8780040acd51e74f27910638fa836e` (merged `main` including #501)
  - `PR502`: `357ab64a0a3fadebac89f0fcfbea3e6be9a0b0cb` (draft PR #502, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `596487c47f6723af110479e0a9b9f910c262d1a9`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR502` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9782** | 1.0001 | **0.8263** | 1.0051 | **0.9821** | `resources/bug_1396264.pdf` (`1.0402`) | **0** | 2 |
| **Direct FFI** | **0.9772** | 1.0005 | **0.8288** | **0.9953** | **0.9816** | `wrapped/synthetic-256-L-smooth-lossy.pdf` (`1.0167`) | **0** | 1 |
| **OpenJPEG2 (unchanged control)** | 1.0000 | 0.9999 | 0.9939 | 0.9984 | 1.0010 | `resources/pixel/jpxdecode_indexed2.pdf` (`1.0310`) | 0 | 7 |

### HT Workloads (4 HT Images + 4 Wrapped HT PDFs)

| Workload | Shim `PR502/Base` (p50 ms) | FFI `PR502/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `ht/256-RGB-noise-lossless.j2k` | **0.7664** (`17.956 -> 13.835`) | **0.7693** (`17.930 -> 13.767`) | 1.0012 |
| `ht/1024-L-noise-lossless.j2k` | **0.7767** (`98.753 -> 76.706`) | **0.7814** (`97.358 -> 77.345`) | 0.9968 |
| `ht/1024-RGB-noise-lossless.j2k` | **0.7863** (`301.419 -> 236.878`) | **0.7844** (`300.531 -> 234.455`) | 0.9978 |
| `ht/256-L-smooth-lossless.j2k` | **0.9960** (`1.998 -> 1.989`) | **1.0006** (`1.963 -> 1.948`) | 0.9799 |
| `wrapped/ht-256-RGB-noise-lossless.pdf` | **0.7834** (`18.910 -> 14.717`) | **0.7796** (`18.784 -> 14.711`) | 1.0025 |
| `wrapped/ht-1024-L-noise-lossless.pdf` | **0.8133** (`109.677 -> 89.199`) | **0.7889** (`107.024 -> 86.771`) | 1.0086 |
| `wrapped/ht-1024-RGB-noise-lossless.pdf` | **0.7962** (`316.667 -> 252.135`) | **0.7895** (`315.140 -> 251.117`) | 1.0013 |
| `wrapped/ht-256-L-smooth-lossless.pdf` | **1.0069** (`2.467 -> 2.487`) | **0.9918** (`2.454 -> 2.426`) | 0.9911 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0` (Shim max `1.0402`, FFI max `1.0167`)
- **Unchanged OpenJPEG2 medians > 1.05:** `0`
- **Rust Shim p90 > 1.05 (2 rows, both `< 0.93 ms`):**
  - Shim `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf`: p50 `0.9874`, p90 ratio `1.2318` (rounds `1.251/1.232/0.873`, `0.758 -> 0.915 ms`)
  - Shim `embedded/98cfa38a-280.jp2`: p50 `0.9923`, p90 ratio `1.2098` (rounds `1.227/1.025/1.210`, `0.767 -> 0.928 ms`)
- **Rust FFI p90 > 1.05 (1 row, `< 0.93 ms`):**
  - FFI `resources/pixel/jpxdecode_indexed2.pdf`: p50 `0.9947`, p90 ratio `1.0972` (rounds `1.013/1.097/1.229`, `0.855 -> 0.921 ms`)
- **Unchanged OpenJPEG2 p90 > 1.05 (7 rows):** `resources/pixel/jpxdecode_without_smaskindata.pdf` (`1.4553`), `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.3208`), `synthetic/256-RGB-smooth-lossless.jp2` (`1.1628`), `resources/pixel/jpxdecode_indexed2.pdf` (`1.1106`), `embedded/8ac3ec64-256.jp2` (`1.0969`), `resources/pixel/jpxdecode_without_colorspace.pdf` (`1.0906`), `wrapped/ht-256-L-smooth-lossless.pdf` (`1.0560`).

No merge, release, backport, runtime change, or #474 closure was performed.
