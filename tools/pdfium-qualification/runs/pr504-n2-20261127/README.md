# PR504 exact-source N2/LLVM24 PDFium qualification (`Base abea3a3` vs `PR504 f72f5dd`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `abea3a339689afdf39f37244de9d0f1ecfe10a69` (current merged `main` including #503)
  - `PR504`: `f72f5dd94527d70e5e8a168750c1f871c8788727` (draft PR #504, `perf/bulk-alloc-zero-band-dwt-474`, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `c5191cae8fdd98861c3d9c5c3988bda81ebace29`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR504` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 16 Synthetic Geomean | 4 HT Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9367** (`-6.33%`) | **0.9442** (`-5.58%`) | **0.9033** (`-9.67%`) | **0.8839** (`-11.61%`) | **0.9455** (`-5.45%`) | `resources/pixel/jpxdecode.pdf` (`1.0233`) | **0** | 4 |
| **Direct FFI** | **0.9383** (`-6.17%`) | **0.9457** (`-5.43%`) | **0.9116** (`-8.84%`) | **0.8924** (`-10.76%`) | **0.9454** (`-5.46%`) | `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf` (`1.0321`) | **0** | **0** |
| **OpenJPEG2 (unchanged control)** | 1.0017 | 0.9995 | 0.9996 | 1.0055 | 1.0022 | `resources/pixel/jpxdecode.pdf` (`1.0431`) | 0 | 5 |

### Selected Bulk-Alloc & Zero-Band/Zero-Detail DWT Wins

| Workload | Shim `PR504/Base` (p50 ms) | FFI `PR504/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `ht/256-L-smooth-lossless.j2k` | **0.7407** (`2.001 -> 1.482`) | **0.7549** (`1.970 -> 1.496`) | 0.9972 |
| `wrapped/synthetic-256-RGB-smooth-lossless.pdf` | **0.7868** (`8.228 -> 6.523`) | **0.8008** (`8.059 -> 6.414`) | 0.9997 |
| `wrapped/ht-256-L-smooth-lossless.pdf` | **0.7885** (`2.432 -> 1.885`) | **0.7963** (`2.406 -> 1.895`) | 0.9985 |
| `synthetic/256-RGB-smooth-lossless.jp2` | **0.8028** (`7.815 -> 6.245`) | **0.7957** (`7.614 -> 6.016`) | 0.9941 |
| `resources/pixel/bug_304.pdf` | **0.8222** (`58.927 -> 48.372`) | **0.8160** (`59.579 -> 48.440`) | 1.0034 |
| `synthetic/256-L-smooth-lossless.jp2` | **0.8286** (`2.720 -> 2.277`) | **0.8466** (`2.718 -> 2.301`) | 0.9870 |
| `resources/pixel/lzw1.pdf` | **0.8370** (`67.364 -> 56.382`) | **0.8628** (`67.243 -> 57.104`) | 1.0027 |
| `embedded/5e4434bd-257.jp2` | **0.8396** (`65.253 -> 54.788`) | **0.8488** (`66.261 -> 55.878`) | 0.9966 |
| `resources/jpx_lzw.pdf` | **0.8438** (`68.483 -> 57.941`) | **0.8389** (`68.063 -> 56.070`) | 1.0097 |
| `embedded/53ccd6a1-271.jp2` | **0.8441** (`1177.162 -> 999.804`) | **0.8499** (`1160.509 -> 983.719`) | 1.0349 |
| `wrapped/synthetic-1024-L-smooth-lossless.pdf` | **0.8594** (`52.317 -> 44.685`) | **0.8581** (`52.454 -> 46.597`) | 0.9865 |
| `synthetic/1024-L-smooth-lossless.jp2` | **0.8626** (`50.958 -> 43.958`) | **0.8695** (`51.250 -> 42.896`) | 0.9995 |

### Retained Adverse Rows (All > 1.05 Median/p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0` (Shim max `1.0233`, FFI max `1.0321`)
- **Unchanged OpenJPEG2 medians > 1.05:** `0` (max `1.0431`)
- **Rust Shim p90 > 1.05 (4 rows, all `< 1.17 ms`):**
  - Shim `resources/pixel/jpxdecode.pdf`: p50 `1.0233`, p90 ratio `1.2258` (rounds `1.027/1.255/1.226`, `0.928 -> 1.133 ms`; unchanged OpenJPEG2 also `1.1931`)
  - Shim `resources/pixel/jpxdecode_with_mismatch_colorspace.pdf`: p50 `1.0159`, p90 ratio `1.1945` (rounds `1.194/0.946/1.294`, `0.741 -> 0.879 ms`)
  - Shim `resources/pixel/jpxdecode_indexed.pdf`: p50 `1.0075`, p90 ratio `1.1599` (rounds `1.160/0.947/1.198`, `1.010 -> 1.166 ms`)
  - Shim `resources/pixel/jpxdecode_without_colorspace.pdf`: p50 `1.0201`, p90 ratio `1.1176` (rounds `0.966/1.129/1.118`, `0.962 -> 1.050 ms`; unchanged OpenJPEG2 also `1.1029`)
- **Rust FFI p90 > 1.05:** **0 rows**.
- **Unchanged OpenJPEG2 p90 > 1.05 (5 rows):** `resources/pixel/jpxdecode.pdf` (`1.1931`), `synthetic/256-RGB-smooth-lossless.jp2` (`1.1374`), `resources/pixel/jpxdecode_without_colorspace.pdf` (`1.1029`), `wrapped/synthetic-256-L-smooth-lossy.pdf` (`1.0625`), `resources/pixel/jpxdecode_without_smaskindata.pdf` (`1.0553`).

No merge, release, backport, runtime change, or #474 closure was performed.
