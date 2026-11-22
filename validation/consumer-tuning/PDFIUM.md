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
for inspection/decode and rejected pixel layouts; successful rendering is not
logged or timed differently. The original C++ debug-only logger is unchanged.

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
