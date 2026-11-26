# PR499 exact-source N2/LLVM24 PDFium qualification (`Base bd02fd0` vs `PR499 0afc716`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `bd02fd0c2b7f293773b75c3ec973115454010b61` (merged `main` including #498)
  - `PR499`: `0afc716a65133ed7f3f587ab3e5906241a344a53` (draft PR #499, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `974060af63e057d2e739d22b42056f26a03aaf39`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR499` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9839** | **0.9764** | 1.0028 | **0.9948** | **0.9834** | `resources/bug_1396264.pdf` (`1.0243`) | **0** | 1 |
| **Direct FFI** | **0.9851** | **0.9725** | 1.0060 | **0.9934** | **0.9870** | `wrapped/ht-1024-L-noise-lossless.pdf` (`1.0336`) | **0** | 4 |
| **OpenJPEG2 (unchanged control)** | 1.0032 | 0.9998 | 0.9999 | 1.0079 | 1.0042 | `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.0375`) | 0 | 4 |

### Selected Legacy Synthetic, Embedded, and Real PDF Wins

| Workload | Shim `PR499/Base` (p50 ms) | FFI `PR499/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `resources/pixel/bug_1469.pdf` | **0.8987** (`5.861 -> 5.255`) | **0.9085** (`5.759 -> 5.241`) | 0.9937 |
| `synthetic/256-RGB-noise-lossless.jp2` | **0.9270** (`56.881 -> 52.613`) | **0.9319** (`56.541 -> 52.534`) | 0.9993 |
| `synthetic/1024-L-noise-lossless.jp2` | **0.9392** (`305.345 -> 286.769`) | **0.9331** (`305.514 -> 285.090`) | 0.9996 |
| `synthetic/1024-RGB-noise-lossless.jp2` | **0.9360** (`918.736 -> 864.514`) | **0.9352** (`917.084 -> 859.689`) | 1.0001 |
| `synthetic/256-L-noise-lossless.jp2` | **0.9389** (`18.835 -> 17.656`) | **0.9397** (`18.885 -> 17.691`) | 1.0025 |
| `wrapped/synthetic-1024-L-noise-lossless.pdf` | **0.9357** (`316.780 -> 296.405`) | **0.9380** (`316.121 -> 296.524`) | 0.9985 |
| `wrapped/synthetic-1024-RGB-noise-lossless.pdf` | **0.9369** (`947.952 -> 888.124`) | **0.9383** (`940.880 -> 882.368`) | 0.9983 |
| `synthetic/1024-RGB-smooth-lossless.jp2` | **0.9608** (`171.485 -> 163.978`) | **0.9556** (`170.313 -> 162.240`) | 1.0011 |
| `wrapped/synthetic-1024-RGB-smooth-lossy.pdf` | **0.9630** (`237.111 -> 231.752`) | **0.9579** (`235.095 -> 228.856`) | 1.0011 |
| `embedded/77e45cf2-264.jp2` | **0.9823** (`454.196 -> 440.844`) | **0.9913** (`440.924 -> 437.107`) | 0.9970 |
| `corpus/fx/action/123.pdf` | **0.9871** (`475.558 -> 485.581`) | **0.9863** (`480.033 -> 477.467`) | 1.0015 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0` (Shim max `1.0243`, FFI max `1.0336`)
- **Unchanged OpenJPEG2 medians > 1.05:** `0`
- **Rust Shim p90 > 1.05 (1 row):**
  - Shim `resources/pixel/jpxdecode_indexed2.pdf`: p50 `1.0170`, p90 ratio `1.0768` (rounds `1.002/1.077/1.150`, `0.921 -> 0.992 ms`)
- **Rust FFI p90 > 1.05 (4 rows, all `<= 2.06 ms`):**
  - FFI `resources/pixel/jpxdecode_smask_in_data_2.pdf`: p50 `0.9904`, p90 ratio `1.2360` (rounds `1.728/1.236/1.000`, `0.410 -> 0.694 ms`)
  - FFI `resources/pixel/jpxdecode_indexed2.pdf`: p50 `1.0069`, p90 ratio `1.1560` (rounds `1.018/1.216/1.156`, `0.940 -> 1.116 ms`)
  - FFI `resources/bug_1396264.pdf`: p50 `0.9970`, p90 ratio `1.0511` (rounds `1.051/1.079/1.033`, `1.959 -> 2.057 ms`)
  - FFI `resources/pixel/jpxdecode_indexed.pdf`: p50 `0.9955`, p90 ratio `1.0507` (rounds `1.051/1.156/0.966`, `1.120 -> 1.176 ms`)
- **Unchanged OpenJPEG2 p90 > 1.05 (4 rows):** `embedded/8ac3ec64-255.jp2` (`1.1333`), `resources/pixel/jpxdecode_without_colorspace.pdf` (`1.1038`), `resources/pixel/jpxdecode_without_smaskindata.pdf` (`1.0922`), `resources/bug_1396264.pdf` (`1.0511`).

No merge, release, backport, runtime change, or #474 closure was performed.
