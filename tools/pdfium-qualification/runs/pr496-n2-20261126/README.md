# PR496 exact-source N2/LLVM24 PDFium qualification (`Base 7790a4e` vs `PR496 b51a413`)

## Complete Qualification Receipt

- **Sources (freshly built and executed, no historical Base substitution):**
  - `Base`: `7790a4ee1237f6af7253109bf797f1d1e669bf5e` (merged `main` including #492/#493/#494)
  - `PR496`: `b51a41301aa83b6d71d902ca0dbb6c0dcea628c0` (draft PR #496, refs #474)
- **Immutable harness:** `90dd9f013c35739a7d67de869180b62a08bcea23` (`tools/pdfium-qualification`)
- **Functional-only checkpoint commit:** `b6e06f07f5132e3fea172d178e0c39a9c175d463`
- **Environment:** Native Neoverse-N2 ARM64 (shared host), CPU 2, Clang `c3223914b508` / Chromium rustc `41b321963` (LLVM 24), PDFium `68f43efa` (prepared `fde5c34a`), `pdfium_tests` `2bcc4fdc`, Hayro `e7ada135`, default features, 2 GiB `RLIMIT_DATA` cap, C/C++ O3/native/ThinLTO/NDEBUG, Rust opt3/native/CGU1/linker-plugin-LTO, final `--lto-O3`. Unchanged OpenJPEG2 binary `b7a74c7901802caefe44b380bc9b3d1779d530b6b9c8462ba7fd0cba9d295b53`.

## Functional, Reference, Diagnostic, and Unit Test Gates

- **Targeted PDFium unit tests:** **46/46 PASS** (`17 Shim + 6 FFI` per source, 0 failures/errors/disabled).
- **Functional gate (`2,521` configurations / `7,563` represented outcomes per source; `12,605` actual functional processes):** `Base` PASS (`0` diffs), `PR496` PASS (`0` diffs), `compare_runs.py` PASS (`0` diffs).
- **Actual stderr diagnostic parity:** `7,563/7,563` matched (`0` differences).
- **Independent reference controls:** `20/20` (`10/source`) executed and preserved.

## Paired 3-Round Performance Summary (`390` source/case-rounds, `1,170` fresh timed processes on CPU 2)

Three-round paired ratios and fixed-cohort geometric means are descriptive, not confirmatory CIs or population-tail proof. No per-process RSS attribution was fabricated.

| Backend | All 65 Geomean | 4 HT Images Geomean | 16 Synthetic Geomean | 6 Embedded Geomean | 39 PDFs Geomean | Worst Median Case | Medians > 1.05 | p90 > 1.05 |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| **Shim** | **0.9828** | **0.8520** | 1.0059 | 0.9943 | 0.9861 | `synthetic/1024-RGB-smooth-lossy.jp2` (`1.0156`) | **0** | 2 |
| **Direct FFI** | **0.9838** | **0.8516** | 1.0031 | 0.9965 | 0.9886 | `resources/pixel/jpxdecode_without_colorspace.pdf` (`1.0252`) | **0** | 3 |
| **OpenJPEG2 (unchanged control)** | 1.0009 | 1.0043 | 1.0015 | 1.0073 | 0.9994 | `embedded/98cfa38a-280.jp2` (`1.0500`) | 0 | 5 |

### HT Workloads (4 HT Images + 4 Wrapped HT PDFs)

| Workload | Shim `PR496/Base` (p50 ms) | FFI `PR496/Base` (p50 ms) | OpenJPEG2 Control |
|---|---:|---:|---:|
| `ht/256-L-smooth-lossless.j2k` | **0.7193** (`3.017 -> 2.174`) | **0.7197** (`2.996 -> 2.147`) | 1.0134 |
| `ht/1024-RGB-noise-lossless.j2k` | **0.8912** (`351.175 -> 312.699`) | **0.8957** (`347.334 -> 312.385`) | 1.0064 |
| `ht/1024-L-noise-lossless.j2k` | **0.8969** (`116.596 -> 104.289`) | **0.8954** (`116.603 -> 103.929`) | 0.9960 |
| `ht/256-RGB-noise-lossless.j2k` | **0.9166** (`20.194 -> 18.526`) | **0.9113** (`20.245 -> 18.523`) | 1.0015 |
| `wrapped/ht-256-L-smooth-lossless.pdf` | **0.7799** (`3.338 -> 2.597`) | **0.7733** (`3.329 -> 2.597`) | 1.0016 |
| `wrapped/ht-1024-RGB-noise-lossless.pdf` | **0.8997** (`355.617 -> 320.552`) | **0.9013** (`355.316 -> 320.313`) | 1.0121 |
| `wrapped/ht-1024-L-noise-lossless.pdf` | **0.9255** (`120.200 -> 112.763`) | **0.9201** (`119.949 -> 111.103`) | 0.9977 |
| `wrapped/ht-256-RGB-noise-lossless.pdf` | **0.9122** (`21.177 -> 19.317`) | **0.9257** (`20.980 -> 19.292`) | 1.0074 |

### Retained Adverse Rows (All > 1.05 p90 Rows Preserved, Not Waived)

- **Rust medians > 1.05:** `0`
- **Rust p90 > 1.05 (5 rows — 2 Shim, 3 FFI):**
  - Shim `ht/256-RGB-noise-lossless.j2k`: p50 `0.9166`, p90 ratio `1.1038` (rounds `1.104/1.117/1.089`, `20.567 -> 22.662 ms`)
  - Shim `wrapped/ht-256-RGB-noise-lossless.pdf`: p50 `0.9122`, p90 ratio `1.0883` (rounds `1.096/1.075/1.088`, `21.185 -> 23.076 ms`)
  - FFI `resources/pixel/jpxdecode_smask_in_data_2.pdf`: p50 `1.0170`, p90 ratio `1.1993` (rounds `1.017/1.199/1.721`, `0.413 -> 0.710 ms`)
  - FFI `wrapped/ht-256-RGB-noise-lossless.pdf`: p50 `0.9257`, p90 ratio `1.0928` (rounds `1.118/1.093/1.093`, `21.179 -> 23.308 ms`)
  - FFI `ht/256-RGB-noise-lossless.j2k`: p50 `0.9113`, p90 ratio `1.0814` (rounds `1.105/1.067/1.081`, `20.665 -> 22.348 ms`)
- **Unchanged OpenJPEG2 p90 > 1.05 (5 rows):** `ht/256-L-smooth-lossless.j2k` (`1.6479`), `synthetic/256-L-smooth-lossless.jp2` (`1.5100`), `synthetic/256-L-smooth-lossy.jp2` (`1.3855`), `embedded/8ac3ec64-256.jp2` (`1.1015`), `resources/pixel/jpxdecode_smask_in_data_2.pdf` (`1.0978`).

No merge, release, backport, runtime change, or #474 closure was performed.
