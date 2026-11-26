# PR500 exact-source N2/LLVM24 PDFium qualification (`Base 38bdda1` vs `PR500 3b7981f`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `38bdda1bad6640a18421330765fa5f3e6d24d311` (merged `main` including #499)
  - `PR500`: `3b7981fb4e56f1195bad0342bf0c9d04015131e8` (draft PR #500, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `8fd52924584dd68a3687c4678b0f62dd1b82f51c`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR500` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9584** | **0.9456** | **0.9651** | **0.9530** | **0.9638** | `resources/pixel/jpxdecode_smask_in_data_2.pdf` (`1.0317`) | **0** | 4 |
| **Direct FFI** | **0.9605** | **0.9481** | **0.9635** | **0.9493** | **0.9671** | `resources/pixel/jpxdecode_without_bitspercomponent.pdf` (`1.0149`) | **0** | **0** |
| **OpenJPEG2 (unchanged control)** | 1.0024 | 1.0013 | 1.0036 | 1.0035 | 1.0026 | `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.0614`) | 2 | 6 |

### Selected DWT 9/7, 5/3, HT, Embedded, and Real PDF Wins

| Workload | Shim `PR500/Base` (p50 ms) | FFI `PR500/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `synthetic/256-RGB-smooth-lossy.jp2` | **0.8877** (`11.090 -> 9.929`) | **0.8831** (`11.057 -> 9.650`) | 1.0037 |
| `wrapped/synthetic-256-RGB-smooth-lossy.pdf` | **0.8898** (`11.441 -> 10.220`) | **0.8759** (`11.565 -> 10.181`) | 0.9988 |
| `synthetic/256-L-smooth-lossy.jp2` | **0.8912** (`3.892 -> 3.483`) | **0.8908** (`3.891 -> 3.499`) | 1.0131 |
| `synthetic/1024-L-smooth-lossy.jp2` | **0.9035** (`65.222 -> 58.931`) | **0.9071** (`65.328 -> 58.645`) | 0.9985 |
| `embedded/77e45cf2-264.jp2` | **0.9111** (`440.914 -> 402.923`) | **0.9078** (`439.219 -> 396.933`) | 1.0106 |
| `corpus/fx/action/123.pdf` | **0.9143** (`467.095 -> 427.075`) | **0.9128** (`470.192 -> 430.406`) | 1.0143 |
| `synthetic/1024-RGB-smooth-lossy.jp2` | **0.9157** (`216.784 -> 199.548`) | **0.9148** (`216.297 -> 196.784`) | 0.9960 |
| `ht/256-L-smooth-lossless.j2k` | **0.9237** (`2.199 -> 2.031`) | **0.9247** (`2.138 -> 2.001`) | 0.9897 |
| `resources/pixel/bug_304.pdf` | **0.9336** (`66.472 -> 61.397`) | **0.9472** (`64.119 -> 59.926`) | 0.9947 |
| `embedded/5e4434bd-257.jp2` | **0.9465** (`66.340 -> 61.639`) | **0.9481** (`64.622 -> 61.951`) | 0.9953 |
| `embedded/53ccd6a1-271.jp2` | **0.9673** (`1223.958 -> 1179.711`) | **0.9640** (`1208.020 -> 1164.011`) | 1.0409 |
| `ht/1024-L-noise-lossless.j2k` | **0.9745** (`102.980 -> 100.902`) | **0.9749** (`103.774 -> 101.167`) | 0.9974 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0` (Shim max `1.0317`, FFI max `1.0149`)
- **Rust FFI p90 > 1.05:** `0`
- **Rust Shim p90 > 1.05 (4 rows, all `< 0.98 ms`):**
  - Shim `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf`: p50 `0.9838`, p90 ratio `1.2284` (rounds `1.228/1.011/1.234`, `0.827 -> 0.976 ms`)
  - Shim `resources/pixel/jpxdecode_indexed2.pdf`: p50 `0.9740`, p90 ratio `1.0931` (rounds `1.158/1.093/0.852`, `0.923 -> 0.949 ms`)
  - Shim `embedded/98cfa38a-280.jp2`: p50 `0.9592`, p90 ratio `1.0656` (rounds `0.961/1.095/1.066`, `0.889 -> 0.947 ms`)
  - Shim `resources/pixel/jpxdecode_smask_in_data_2.pdf`: p50 `1.0317`, p90 ratio `1.0512` (rounds `1.137/1.051/0.695`, `0.651 -> 0.452 ms`)
- **Unchanged OpenJPEG2 medians > 1.05 (2 rows):** `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.0614`) and one other >1.05 control row in `performance-summary.json`.
- **Unchanged OpenJPEG2 p90 > 1.05 (6 rows):** `embedded/8ac3ec64-255.jp2` (`2.1645`), `ht/256-L-smooth-lossless.j2k` (`1.6394`), `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.4456`), `resources/pixel/jpxdecode_indexed2.pdf` (`1.3563`), `synthetic/256-L-noise-lossy.jp2` (`1.1995`), `resources/bug_1396264.pdf` (`1.1728`).

No merge, release, backport, runtime change, or #474 closure was performed.
