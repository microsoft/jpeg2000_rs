# Separate actual PDFium consumer

This follows [the public #449 handoff](https://github.com/microsoft/jpeg2000_rs/issues/449#issuecomment-7071726628),
using Gerrit CL 164990 patch set 2 (`ec9185e7d6b973d453f2fe6bf1d9eb9a1eb9ebc3`).
Its original dependency is `89a85673266d204937025399ee921286dbce9c12`, not 0.2.2.
The driver explicitly rolls DEPS to published source anchor
`4989f9c680beeb7bad4fbfd441a93aa373d2ba4f`, regenerates the GN source list from
that actual checkout, and adapts the bridge's now-private JP2 fields to
their public getters. The correct four-byte `jP  ` signature is validated
against the raw pinned source, not inferred from HTML-rendered spacing.
Decoder source is not modified.
The owned experimental Rust bridge retains failure-only release diagnostics
for inspection/decode and rejected pixel layouts. Normal successful attempts
are not logged. A recovered image still logs its failed initial strict attempt;
the observational recovery timings include this diagnostic overhead.
The original C++ debug-only logger is unchanged.

Use a fresh directory outside an existing Cargo/PDFium workspace. The pinned
depot_tools is `96a7c1418eedaa6bea333a8941e8a0078681b4d0`; auto-update is disabled.
Its supported `ensure_bootstrap` initializes the owned Python/CIPD helpers
without updating that source checkout; inherited depot_tools roots are not used.
The minimal checkout still explicitly includes Rust, the decoder and matched
testing corpus. At least 12 GiB is required; never free space by deleting
shared user data.

```sh
python3 pdfium_integration.py prepare --work-root /new/pdfium-consumer
python3 pdfium_integration.py run --work-root /new/pdfium-consumer \
  --output /new/pdfium-results
```

All optimized GN configurations use the same compiler, renderer and inputs,
with V8, XFA and Skia disabled. The strict Rust/OpenJPEG pair keeps recovery
disabled. A separately labeled bounded-recovery Rust variant is also measured;
it is not substituted for strict qualification.
Cargo profile variables do not configure GN. Actual Ninja compiler/link commands
and final link-step durations are preserved, with build time, RSS, executable
size and `.text` separate.
Rust wrapper flag dumps and their expanded response files are preserved too:
the Ninja wrapper invocation alone does not expose the effective codegen flags.
Ninja command output is retained verbatim even if it contains non-UTF-8 bytes;
only its human-readable JSON rendering escapes them. Built executables are
preserved before subsequent diagnostics so a logging failure cannot erase them.

The unchanged pixel/corpus runners select the supplied `bug_304.pdf` and
`fx/action/123.pdf` expectations. Missing inputs, failed golden tests and
unsupported configurations remain visible. Actual OpenJPEG/Rust rendered
page parity is checked with `pdfium_diff` before comparing timings; failures
produce no speed claim. Eight reversed process pairs use warm filesystem
caches and fresh processes, timing the entire PDFium invocation including
parse/decode/render/PNG output. Per-case median/p90 and paired uncertainty
are therefore not isolated decoder timings or a substitute for zune results.

The matched `bug_304` streams contain a trailing PDF EOL after EOC. Published
0.2.2 rejects that trailing data in strict mode and accepts it only through
bounded PDF recovery. Its strict parity failure remains visible, rather than
silently trimming input or reporting a recovery result as strict acceptance.

No expected image is regenerated or ignored, no private PDF input is uploaded,
and source/proof/package/default-profile or publication policy is unchanged.

## Completed native observations

[Hosted run 44979836962](https://github.com/microsoft/jpeg2000_rs/actions/runs/44979836962)
at `c035ae4` completed all three actual optimized GN builds on **EPYC 9V45**,
not the earlier zune EPYC 9V74. An independent owned native **EPYC 7763** run
at `92113a4` completed the same builds and additionally preserved effective
Rust flag dumps and expanded response files. Neither is a Cargo substitute.

| Case | Strict Rust | Bounded-recovery Rust | Exact page/golden disposition |
|---|---|---|---|
| `bug_304` | Correctly rejects trailing EOL; blank page | Accepts all four JPX images | Recovery page matches OpenJPEG exactly; pixel runner passes |
| `action_123` | Accepts, decodes and renders | Same rendered bytes | Both differ numerically from OpenJPEG; corpus runner fails; no timing comparison |

The valid `action_123` page is **not blank or rejected**. Debugging the actual
preserved GN executable shows inspection, decode and pixel writing all return
true and receive the independently extracted 49,979-byte stream, SHA256
`7905e1a5c74eefe6bf072cab50cd6f40aac2834273fee241926e783b8357d8d6`.
The 595x841 rendered page differs at 73.7633% of pixels, but maximum absolute
channel difference is **4**, mean absolute difference **0.438286/255**.
This is a numerical comparison failure, not a missing-acceptance diagnosis.
The exact golden/parity gate is unchanged; its timing remains null.

Rust valid-page PNG SHA256 is
`1997f0e9c61e5519e2c7886174439702ba043a12676d6aa11388a5a0d7a88245`
in the original strict run, corrected hosted strict/recovery run and owned
native strict/recovery run. Diagnostic/source-roll changes do not change
the successful output.

Both native hosts record suite exit codes:
OpenJPEG pixel/corpus **0/0**, strict Rust **1/1**, recovery Rust **0/1**.
These failures are explicit and are not converted into all-green qualification.
The strict invalid-input and valid numerical-difference cases have no timing
comparison. Only the exact lossless recovery page is compared:

| Native host | Rust/OpenJPEG paired elapsed ratio [95%] |
|---|---:|
| EPYC 9V45 | 6.92763 [6.84414, 7.01336] |
| EPYC 7763 | 6.59279 [6.48608, 6.70560] |

Each host contributes eight reversed process pairs. Hosted median/p90 times
are OpenJPEG **18.19/18.71 ms**, Rust recovery **125.80/128.72 ms**.
These include parse, four image decodes, rendering, PNG output, process
startup and failed-strict-attempt diagnostics. They are **not a build-tuning
win**, an isolated decoder comparison or pooled cross-host evidence.

### Actual GN configuration audit

The pinned DEPS install Chromium Rust **1.101.0-nightly**
(`8a9dd7abdf013ec10cfeaaa3685feba18ef1c90c`) and Clang **24.0.0git**
(`e063be79adf127cce301fe5948273102a33012b6`), not the Cargo study's Rust 1.93.1.
Build repository commit is `0c62137b8623a3fab2c6aa5d7c94f719b3aa31f6`.
Compiler version/hash receipts are retained with the owned native results.

There are 48 actual Rust flag dumps per Rust variant. The decoder's expanded
arguments include `--target=x86_64-unknown-linux-gnu`, `-Copt-level=3`,
`-Cembed-bitcode=no`, **`-Clto=no`**. There is **no explicit target CPU or
codegen-units override**; do not infer either from Cargo variables or describe
this as ThinLTO/CGU1. The Rust/recovery decoder response files are identical,
SHA256 `d36b5ef5c7fd0d4810b58a424f5bd3e4281f6e0c116783f60569fe5446fc8341`.
Their linked decoder rlibs are byte-identical too, SHA256
`8f1fafec935c75796d1d7e94bf8337ded88d1ec22e15ace51d9968bfb0eb4c5a`.
Recovery is a separately enabled consumer policy, not a decoder rewrite.

Single cold build observations, with two build jobs and no cache-drop:

| Host/variant | Build s | Final `pdfium_test` link ms | Peak build-process KiB |
|---|---:|---:|---:|
| 9V45 OpenJPEG | 228.48 | 172 | 540464 |
| 9V45 strict Rust | 268.58 | 160 | 1141964 |
| 9V45 recovery Rust | 270.46 | 155 | 1142780 |
| 7763 OpenJPEG | 384.79 | 240 | 538532 |
| 7763 strict Rust | 428.45 | 231 | 1146352 |
| 7763 recovery Rust | 428.19 | 232 | 1150800 |

The binaries on both hosts have the same sizes:
OpenJPEG **6,611,240 bytes / `.text` 3,094,956**;
strict Rust **7,080,984 / 3,326,476**;
recovery Rust **7,081,048 / 3,326,540**.
These are executable/section sizes, not a stripped-production comparison.
Median peak process RSS for the qualified recovery page is
**11.10/36.42 MiB** OpenJPEG/Rust on 9V45 and **10.65/35.99 MiB** on 7763.
It includes the full PDFium process and PNG output, not isolated allocations.
Raw sampled-tree RSS and all per-process observations remain available.

### Recommendation and receipts

Keep portable defaults and the original strict policy. This completes the
relevant actual-GN configuration/output audit, but establishes **no GN
CPU/LTO/CGU speed recommendation** and no universal OpenJPEG pixel interchangeability.
The actual zune tuning results are separately reported in
[ZUNE_RESULTS.md](ZUNE_RESULTS.md). Core source, package/proof qualification and
published 0.2.2 remain unchanged.

[The actual evidence index](actual-evidence.json) locates full hosted/owned
results, source/toolchain receipts, debugger input hashes, preserved failed attempts
and native binaries. Generated results are outside tracked source.
[Hosted artifact 14737293329](https://github.com/microsoft/jpeg2000_rs/actions/runs/44979836962/artifacts/14737293329)
expires **2026-12-22 03:31:05 UTC**. Host-local retention is not indefinite.

Two discarded diagnostic attempts are not counted as qualification:
`44976132115` stopped at a mistaken whitespace guard before changing the
already-correct raw signature; `44977828206` stopped when the pinned compiler
rejected exposing the original C++ logger in release. The corrected Rust
producer diagnostics compile, preserve normal output and keep those failures
visible. No incorrect signature edit or compiler-policy suppression was applied.
