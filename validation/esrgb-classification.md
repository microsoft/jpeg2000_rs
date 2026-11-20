# Issue #439: e-sRGB classification and normative blocker

This is a blocked correction, **not** an e-sRGB implementation or issue-closure
claim. Production code, semantic models, public APIs, output policies, allocation
owners and error priority are unchanged. Native acceptance is not a colour
conversion, and neither native acceptance nor Hayro's RGB output proves
conformance or supplies a colorimetric oracle.

## Exact input and provenance

The original file is
[`fixtures/hayro-esrgb/jp2_colr_esrgb.jp2`](fixtures/hayro-esrgb/jp2_colr_esrgb.jp2).
It is copied unchanged from Hayro revision
[`e7ada1354dff4041cdeed3d8ba56fe01b6186132`](https://github.com/LaurenzV/hayro/tree/e7ada1354dff4041cdeed3d8ba56fe01b6186132),
path `hayro-jpeg2000/tests/streams/jp2_colr_esrgb.jp2`.
Its SHA-256 is
`1dccce55ca6427f9a9eaa47cdd0d2cf953ea331822a604f60b5c606aefd36af9`.
The adjacent [`LICENSE-MIT`](fixtures/hayro-esrgb/LICENSE-MIT) is the unchanged
upstream `LICENSE-MIT` from that same revision. This test fixture is excluded
from the Rust package and is never accessed with Rust `include_bytes!`.

Inspection of the actual bytes gives:

| Field | Actual value |
|---|---|
| Signature / top-level boxes | JP2 signature, `ftyp`, `jp2h`, one `jp2c` |
| `ftyp`, offset 12, length 20 | Primary brand `jp2 `, minor version 0, compatibility list containing only `jp2 ` |
| `ihdr`, offset 40, length 22 | Width 128, height 96, three components, BPC 7 (unsigned eight-bit), compression 7, `UnkC=0` |
| First and only `colr`, offset 62, length 15 | METH 1, PREC 0, APPROX 0, EnumCS 20; no trailing enumerated parameters |
| Palette / channel metadata | No `pclr`, `cmap`, `cdef`, or `bpcc`; source channels remain in codestream order |
| `jp2c`, offset 77, length 21315 | SIZ describes three unsigned eight-bit, 1-by-1 sampled components; source bytes start at offset 85 |

## Actual acquired normative basis

The acquired PDFs were hash-checked before classification:

* [T.800 (06/2019)](https://www.itu.int/rec/T-REC-T.800-201906-I/en),
  SHA-256 `9932e967462cd56a193db87117917e74734fb385913bf51d1f52fb0428924e1c`:
  I.5.2 distinguishes the primary brand and compatibility list.
  I.5.3.3 and Table I.10 limit the first enumerated `colr` in conforming
  JP2 to 16, 17 and 18. EnumCS 20 is therefore **not a conforming strict JP2
  declaration in this JP2-only-branded fixture**. Raw component acceptance
  in this decoder is not a certification of its container declaration.
  This classifies the declaration under Part 1; it does not invalidate the
  registered JPX colourspace itself.
* [T.801 (06/2021)](https://www.itu.int/rec/T-REC-T.801-202106-S/en),
  SHA-256 `8ec28b54b53f5b6898a02d0718566600809e1c86ecbbf64ab0e1e443e7f67f40`:
  M.11.7.3.1 and Table M.25 define EnumCS 20 as e-sRGB **by reference to
  PIMA 7667**. Annex M supplies the JPX extension; M.8 governs its branding.
  M.8 requires a `jpx ` compatibility entry for conforming JPX files, with
  minor version 1, and a `jpx ` primary brand for files completely defined
  by that Recommendation. This fixture advertises none of those values.
  M.9.2.4 explicitly includes e-sRGB among the JPX baseline colour methods.
  EnumCS 20 is a legal registered JPX colourspace, not an ordinary JP2 sRGB
  alias. The fixture's Part 1 branding alone cannot establish conformance
  to that extension or determine its sample encoding.
* The authoritative
  [IS&T PIMA 7667:2001 legacy-standard catalog](https://www.imaging.org/IST/IST/Store/StoreLayouts/Item_Detail.aspx?iProductCode=PIMA7667-2001)
  identifies a distinct extended-gamut, output-referred encoding. On
  2026-11-20 its full downloadable PDF was offered for purchase ($25,
  member price $20); it was **not acquired**. IEC 61966-2-1 sRGB equations
  alone are not a complete definition of this PIMA encoding.

The [selected editions](../REFERENCES.md#standards) remain T.800 (07/2024)
and T.801 (08/2023). Their full texts are purchase-controlled; this work
neither bypasses access controls nor claims reconciliation with those editions.
No standards text or PDF is redistributed here.

## Distinct acquisition attempts and exact blocker

First, the acquired T.800/T.801 full texts identify the actual legal enumeration
and its external normative dependency. Second, the current authoritative IS&T
catalog establishes how to obtain that dependency. Public-authoritative
searches for an authorized full definition (including IS&T and ICC sources)
did not establish one. Search results exposed unofficial PDF mirrors, but
those PDFs were not fetched or used as normative sources. Search snippets
are not adopted as equations or as proof of permitted precision.

Consequently the source sample coding, permitted precisions, extension range,
offset/scale, transfer function, primaries/reference conditions, and conversion
rounding/clipping for PIMA 7667 have **not** been independently established
from an authorized full source. In particular, this eight-bit fixture does
not establish an eight-bit e-sRGB encoding rule. Constants cannot be inferred
from its samples or copied from Hayro's acceptance.

There are two separate required parent decisions:

1. Supply an authorized PIMA 7667:2001 full source and independently establish
   a meaningful encoding for these source samples, or identify an explicit
   malformed-declaration compatibility policy backed by independent evidence.
   A normative JPX colourspace definition alone cannot validate a JP2-only
   branded fixture. Changing branding alone cannot establish its sample coding.
2. Choose strict rejection versus a narrowly justified opt-in compatibility
   path. If conversion to existing `ConvertedColorSpace::Srgb` cannot be
   justified, distinct accurate output metadata needs an explicit API decision
   before adding a variant that breaks exhaustive downstream matches.

Until then, `decode_jp2` retains the original native planes and
`decode_jp2_color` / `decode_jp2_color_selected` return
`UnsupportedColorConversion { reason: EnumeratedColorSpace }`. No global
container-policy relaxation, silent sRGB replacement, fallback decoder,
experimental constants, manufactured numerical oracle or tolerance change
has been introduced. Unsupported alpha/sampling/association combinations
have not been newly admitted.
This preserves the current implementation's rejection, not a decision that
e-sRGB support is unnecessary or that issue #439 can be closed as unsupported.
The issue remains blocked on normative access and an explicit interpretation.

## Qualification and limits

`validation/tests/test_esrgb_classification.py` uses `framework.build_subject`
and the bounded success/error runner. It checks the pinned original's native
128-by-96 three unsigned eight-bit planes, exact conversion error on full and
selected public callers, and unchanged native planes versus the extracted
codestream. A counterfactual changing only EnumCS 20 to 16 demonstrates that
ordinary sRGB conversion still succeeds; **it is not an e-sRGB oracle**.

The native `esrgb_is_not_silently_relabelled_or_normalized_as_srgb` test exercises
the production dispatcher with eight-, ten-, twelve- and sixteen-bit inputs,
and keeps unsupported-colour priority ahead of output limits and allocation.
It does not assert those precisions are normatively legal for e-sRGB.
Existing colour tests retain grayscale/sRGB/sYCC, channels, geometry and
storage controls. Focused production conversion and actual public-caller
proofs can establish the **existing model refinement and typed rejection**,
not a colour equation absent from that model.

### Measured candidate checks (2026-11-20)

| Check | Result |
|---|---|
| `cargo test --locked --offline color::tests --lib`, Rust 1.93.1 | 31 passed |
| `.venv/bin/python -m unittest discover -s validation/tests -p test_esrgb_classification.py -v`, subject built with Rust 1.93.1 | 2 passed; original native decode and full/selected conversion-error controls |
| `cargo fmt --all --check`, Rust 1.93.1 | Passed |
| `cargo clippy --all-targets --all-features --locked --offline -- -D warnings`, Rust 1.93.1 | Passed |
| `framework.validate_normative_coverage()` | Passed maintained inventory links; no exhaustive standards claim |
| Verus focus `color::conversion` | 10 verified, 0 errors |
| Verus focus `decode::api`, `--verify-function '*decode_jp2_color*'` | 2 verified, 0 errors (full and selected actual public callers) |
| Verus focus `specs::cold_color_conversion` | 42 verified, 0 errors |
| Verus focus `specs::container_colors` | 15 verified, 0 errors |

Each proof command used Verus `0.2026.10.04.426d8b0`, toolchain
`1.98.1-x86_64-unknown-linux-gnu`, and the common arguments
`cargo verus focus --features verus --locked --offline --fwd-verus-args-to roots
--target-dir target/esrgb-verus --lib -- --no-lifetime --verify-only-module MODULE
--output-json` (with the caller function filter as shown). No budgets, trust
boundaries, assumptions, existing Rust-only adapters or exclusions changed.
These are module/function focuses, **not whole-source/package qualification**.
Local JSON/stderr receipts reside under `target/issue439/`.

An additional Clippy attempt on Rust 1.98.1 reported pre-existing lints in
unchanged container/JPIP/JPX files (including `question_mark`, `while_let_loop`
and `manual_checked_ops`); no unrelated code or lint policy was modified.
The project's pinned Rust 1.93.1 strict all-target/all-feature command above
passes. A failed exploratory proof invocation using two `--verify-function`
flags was replaced by the successful complete `specs::container_colors` focus.

Independent normative extended-value/boundary/rounding/clipping vectors
cannot honestly be supplied before resolving the source-definition blocker.
Whole-source, actual-package and final CI/release integration remain the
coordinator's responsibility. No passing regression or focused proof resolves
either normative decision above.
