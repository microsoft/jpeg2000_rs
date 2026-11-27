# PR503 exact-source N2/LLVM24 PDFium qualification (`Base ec5d3f0` vs `PR503 8c82b53`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `ec5d3f038192ef51928bc62600d9f28f127b8003` (merged `main` including #502)
  - `PR503`: `8c82b53e7a97e5163833e5268cb2626d681a04c2` (draft PR #503, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `77050fbb9b934b1ef6687564af3304ad5ea373cc`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR503` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9952** | **0.9888** | **0.9958** | 0.9999 | **0.9971** | `resources/pixel/jpxdecode_smask_in_data_2.pdf` (`1.0354`) | **0** | 3 |
| **Direct FFI** | **0.9959** | **0.9934** | **0.9913** | **0.9971** | **0.9972** | `resources/jpx_lzw.pdf` (`1.0259`) | **0** | 3 |
| **OpenJPEG2 (unchanged control)** | 0.9985 | 1.0005 | 1.0057 | 0.9922 | 0.9979 | `resources/pixel/bug_1012369.pdf` (`1.0197`) | 0 | 6 |

### Selected Post-Tier-1 Vectorization Wins

| Workload | Shim `PR503/Base` (p50 ms) | FFI `PR503/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `synthetic/1024-L-smooth-lossy.jp2` | **0.9688** (`55.433 -> 54.187`) | **0.9863** (`54.988 -> 55.387`) | 1.0064 |
| `synthetic/256-L-smooth-lossy.jp2` | **0.9696** (`3.448 -> 3.336`) | **0.9741** (`3.428 -> 3.339`) | 1.0028 |
| `wrapped/synthetic-256-L-smooth-lossy.pdf` | **0.9718** (`3.798 -> 3.688`) | **0.9701** (`3.816 -> 3.702`) | 0.9875 |
| `synthetic/256-RGB-smooth-lossy.jp2` | **0.9713** (`9.719 -> 9.406`) | **0.9866** (`9.544 -> 9.223`) | 1.0071 |
| `synthetic/1024-RGB-smooth-lossy.jp2` | **0.9771** (`190.465 -> 185.857`) | **0.9721** (`188.636 -> 183.369`) | 0.9999 |
| `wrapped/synthetic-1024-RGB-smooth-lossy.pdf` | **0.9748** (`199.279 -> 193.446`) | **0.9857** (`196.468 -> 194.328`) | 1.0032 |
| `embedded/77e45cf2-264.jp2` | **0.9784** (`394.165 -> 383.752`) | **0.9788** (`388.939 -> 379.952`) | 1.0000 |
| `corpus/fx/action/123.pdf` | **0.9795** (`414.798 -> 407.695`) | **0.9833** (`415.825 -> 408.890`) | 1.0114 |
| `ht/256-L-smooth-lossless.j2k` | **0.9817** (`2.046 -> 2.005`) | **0.9814** (`1.977 -> 1.936`) | 1.0181 |
| `wrapped/ht-256-L-smooth-lossless.pdf` | **0.9936** (`2.453 -> 2.424`) | **0.9807** (`2.455 -> 2.408`) | 1.0060 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0` (Shim max `1.0354`, FFI max `1.0259`)
- **Unchanged OpenJPEG2 medians > 1.05:** `0`
- **Rust Shim p90 > 1.05 (3 rows, all `< 1.18 ms`):**
  - Shim `embedded/98cfa38a-280.jp2`: p50 `0.9960`, p90 ratio `1.1567` (rounds `1.232/1.157/0.958`, `0.793 -> 0.918 ms`)
  - Shim `resources/pixel/jpxdecode_indexed.pdf`: p50 `0.9933`, p90 ratio `1.1109` (rounds `1.073/1.140/1.111`, `1.050 -> 1.179 ms`)
  - Shim `resources/pixel/jpxdecode_smask_in_data_2.pdf`: p50 `1.0354`, p90 ratio `1.0811` (rounds `1.554/1.081/0.959`, `0.427 -> 0.454 ms`)
- **Rust FFI p90 > 1.05 (3 rows, all `< 1.09 ms`):**
  - FFI `resources/pixel/jpxdecode.pdf`: p50 `0.9973`, p90 ratio `1.1659` (rounds `1.188/1.109/1.166`, `0.920 -> 1.081 ms`)
  - FFI `resources/pixel/jpxdecode_without_smaskindata.pdf`: p50 `1.0202`, p90 ratio `1.1576` (rounds `1.158/1.173/0.988`, `0.765 -> 0.885 ms`)
  - FFI `resources/pixel/jpxdecode_without_bitspercomponent.pdf`: p50 `1.0059`, p90 ratio `1.0694` (rounds `1.069/0.970/1.093`, `0.926 -> 0.986 ms`)
- **Unchanged OpenJPEG2 p90 > 1.05 (6 rows):** `wrapped/synthetic-256-L-smooth-lossless.pdf` (`1.1814`), `resources/pixel/jpxdecode.pdf` (`1.1703`), `resources/pixel/bug_1012369.pdf` (`1.1460`), `resources/pixel/jpxdecode_without_colorspace.pdf` (`1.1050`), `ht/256-L-smooth-lossless.j2k` (`1.0975`), `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.0618`).

No merge, release, backport, runtime change, or #474 closure was performed.
