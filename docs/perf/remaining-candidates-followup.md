# Remaining-candidate follow-up

Execution starts 25 November 2026 at 20:38 UTC. **In progress, not an adoption
recommendation.** Original decoder checkout/defaults remain unchanged.

## Coverage and controls

Fresh exports contain 91 issues and 395 PRs. All actual changes since the prior
survey were read: the only new record is draft #494, under #481, implementing
a “private, fallible stable-position tile-part index once for multiple validated
selected tiles.” That is not intra-selected-tile coefficient support, direct
Tier-1 flag contexts, exact MQ charging, or a new floating product representation.
Existing #493 color, #473 integer-wavelet and owner/copy work remain excluded.

Default main remains `f4b2b7b29d38fa31bd74263913462bb67d6e5e4e`.
Every experiment branches from that exact main:

| Scope | Branch | Initial measured/verified source |
|---|---|---|
| C11 counting only | `perf/eval-c11-support-mask` | `c0316ac`; subsequent odd-origin admission fix `509a7c4` |
| C2 direct cached flags | `perf/eval-c2-direct-flags` | `a24966f` |
| C7 exact charge guard | `perf/eval-c7-exact-charge` | `46a9bb8` |
| C4 exact binary64 product | `perf/eval-c4-exact-f64` | `137fda7` |

Paired measurements pin timing harness `76e23b5`, whose Rust/C driver bytes
match the original `50b3c69` control driver exactly. Existing current-main
generic/consumer control binaries are reused with recorded source and binary
identities; the newer container-aware conformance driver is not silently
substituted into a timing comparison.

## C11: non-invasive support-mask experiment

The unpublished tool uses existing public parse/plan/packet APIs. It still
decodes every code-block in each selected tile. There is **no entropy pruning,
work-charge change, new decoder knob, or measured optimization speedup**.

The separable 5/3 mask reverses predict/update dependencies, including symmetric
boundaries and odd origins, then propagates required LL support through levels.
Tests compare masked/unmasked public inverse-5/3 results over every small interval,
including singleton and odd-origin boundaries, and real 2D inverse-kernel crops
through three levels and both origin parities. An actual `(3,5)`-origin encoded
full/selected probe also passes. Registered/non-isotropic layouts outside the
first model are explicitly refused.
Unsupported 9/7 is explicitly refused rather than given an unproven halo.

Observed encoded bytes/passes outside complete support-expanded code-blocks:

| Input/request | Outside blocks | Outside encoded bytes | Outside decoded passes |
|---|---:|---:|---:|
| Untiled 8K, `(2048,2048,512,512)` | 16210 / 16384 | 98.8137% | 98.7963% |
| Untiled 8K, edge 512-square | 16263 / 16384 | 99.1732% | 99.2173% |
| Untiled 8K, odd-origin 511 x 509 | 16221 / 16384 | 98.8583% | 98.8422% |
| Untiled 8K, whole image | 0 / 16384 | 0% | 0% |
| Tiled-256 8K, selected middle/edge/odd windows | 0 / 100 each | 0% | 0% |

This confirms substantial **untiled** eligibility and that existing tile culling
already does useful work. Bytes/passes are not actual MQ decisions or removable
wall-time percentages. A pruning implementation still needs selected/full
refinement, filter-support/geometry admission and exact malformed-input,
allocation/resource and deadline behavior. These counts do not authorize
discarding validation or charging a fictitious coarse work bound.

[Counts](data/followup-c11-support-counts.csv) and
[scope/source identities](data/followup-c11-support-provenance.json).

## C7: exact guarded charging

The common path checks `work < maximum`, adds exactly one, and returns.
The original checked path remains at the frontier, including its increment
before over-limit errors, overflow precedence, offsets and partial state.
There is no pass/block batching or removed clock/safety check.

All 1,385 library tests and five doctests pass; MQ whole-state/frontier tests
include the largest admissible increment and overflow. Deadline controls,
strict Clippy/formatting and actual Rust 1.88 checks pass.

[Pinned run 45699273869](https://github.com/microsoft/jpeg2000_rs/actions/runs/45699273869)
passes **source and actual package: 6,363 obligations / zero errors each**.
All 401 implementation/model input hashes were independently matched to this
source. Existing five Rust-only adapters and `--no-lifetime` remain explicit;
source-function coverage is not measured.

The 24,245 paired samples / 88 measured processes show class changes between
about **-1.43% and +0.24%**, below retention thresholds and mostly within combined
IQR. Representative whole-process instruction reductions are about 0.24-1.11%.
**No-go for this guard alone**, not a claim that every exact batching design
has been exhausted. All 134 full/selected/conformance outcomes, including the
seven existing refusals, and all original #299 controls remain unchanged.

## C2: direct cached-significance contexts

This is **not** the rejected count-LUT experiment. Literal 256-entry tables
index the already cached eight-neighbor significance mask directly. Sign
summary construction is deferred until a positive significance decision;
all-zero cleanup candidacy uses the same masked bits. VSC and all four
orientations remain represented. This is not a claim of four-row stripe
packing or 32/64 const specialization.

All 1,386 library tests and five doctests pass, including exhaustive cached-mask,
orientation, sign and VSC-boundary comparisons. Strict Clippy, formatting,
deadline controls and actual Rust 1.88 checks pass.

[Pinned run 45701323795](https://github.com/microsoft/jpeg2000_rs/actions/runs/45701323795)
translates the literal tables but fails production verification: table/cleanup
postconditions and solver-resource failures, **nine errors**. Package
verification is not qualified. No proof, rlimit or pin is weakened to obtain
a pass.

The 25,589 paired samples / 88 processes are promising: lossless A/C/D subsets
improve about **11.5-14.0%** in both profiles; lossy B is within noise.
Representative lossless instruction reductions are about **16.8-19.7%**.
All 134 output/error outcomes and original #299 controls are unchanged, but
the failed proofs prevent a Go recommendation.

A separate **runtime variant**, `perf/eval-c2-direct-flags-proofs` at `fe3ca8f`,
keeps mask candidacy/deferred sign summaries but computes contexts using existing
verified arithmetic rather than runtime literal arrays. Original arrays remain
test-only golden data. An explicit mask/neighbor equivalence lemma is added,
without assumptions or higher solver budgets. Full 1,386 tests, five doctests,
Clippy and actual MSRV pass. Its
[proof run 45708509798](https://github.com/microsoft/jpeg2000_rs/actions/runs/45708509798)
now passes **source and actual package: 6,371 obligations / zero errors each**,
with all 401 implementation/model hashes independently matched and unchanged
lifetime-disabled/five-adapter boundary.

The **separate** 24,762-sample / 88-process representative run improves A/C/D
by about **7.50-7.99%** in both profiles; B's approximately +0.40% is within
combined IQR for every sampled image. Original #299 controls remain exact.
This is not the first variant's 14% result.

All 134 full/selected/conformance outcomes match for this variant too.
A full 65-case generic/consumer ARM paired escalation is running. The explicit
same-host generic/**x86-64-v3** 57-case paired study completed successfully in
[run 45711245733](https://github.com/microsoft/jpeg2000_rs/actions/runs/45711245733).
Its original 112,599,565-byte ZIP matches the server SHA256; all 4,741 indexed
payloads, 100,185 samples / 456 full-protocol processes / 114 summaries and
48 original Callgrind Ir outcomes were independently verified. The separate
short control-build clocks are not speed evidence.

| Hosted profile | A (6 images) | B (18) | C (14) | D (19) |
|---|---:|---:|---:|---:|
| Generic | -8.393% | +0.361% | -5.190% | -9.368% |
| x86-64-v3 | -9.686% | **+1.416%** | -5.461% | -10.435% |

All 114 outputs match the same-profile current-main control. Representative
lossless guest instructions decrease 14.8-18.0%; the measured B representative
is effectively unchanged. However, the **v3 B class exceeds the 1% slowdown
guard**: 16 of 18 images are within combined IQR, but two are outside it.
This is not dismissed as noise or erased by averaging with another host.
A targeted repeat of all 18 B images and four A/C/D controls is required before
a retention decision. The first matrix is preserved regardless of that result.
See the complete [114 image/profile summaries](data/followup-c2-proof-variant-x86-paired.csv),
[eight class results](data/followup-c2-proof-variant-x86-classes.csv),
[independent artifact/raw validation](data/followup-c2-proof-variant-x86-validation.json),
and [stable instruction comparisons](data/followup-c2-proof-variant-x86-instructions.csv).

Normal CI on the actual
candidate source completed successfully in
[45710713971](https://github.com/microsoft/jpeg2000_rs/actions/runs/45710713971):
all nine required jobs pass, including Rust 1.88, Linux/macOS/Windows tests and
independent numerical checks, generated decoder validation, and quality/package
audit. Six unrelated optional jobs are skipped, not claimed as passes. All four
uploaded numerical/validation ZIPs match their server SHA256 digests. Full ARM
and v3 B confirmation gates remain pending; no Go claim is made yet.

[Distinct variant paired samples summary](data/followup-c2-proof-variant-paired.csv),
[class changes](data/followup-c2-proof-variant-classes.csv) and
[exact source/package receipts](data/followup-c2-proof-variant-verification.json).
Also retained are this variant's own
[134 output/error checks](data/followup-c2-proof-variant-qualification.csv),
[instruction counts](data/followup-c2-proof-variant-instructions.csv), and
[completed normal-CI receipt](data/followup-c2-proof-variant-normal-ci.json).

## C4: exact floating-product alternative

This experiment tests a narrower alternative to changing the entire pipeline
to f32: bounded binary64 products with the existing Q16 result and integer
fallback. With `|value| <= 2^34` and `|factor| <= 2^18`, the integer product plus
rounding bias is exactly representable below 2^53. Flooring after power-of-two
scaling preserves the integer result, including negative ties.

No whole-plane buffer, extra allocation, public representation or tolerance is
changed. This does **not** evaluate or rule out full f32-through-MCT, nor
duplicate the tracked bounded integer/layout kernels.

All 1,386 library tests, five doctests, sign/boundary/fallback-error tests,
deadline controls, strict Clippy/formatting and actual Rust 1.88 checks pass.
[Pinned run 45701331499](https://github.com/microsoft/jpeg2000_rs/actions/runs/45701331499)
fails at the frontend: `std::f64::floor` is unsupported. No suggested
`assume_specification` or proof erasure is introduced. Source/package proofs
therefore do not pass.

The 24,164 paired samples / 88 processes show lossy B **4.90% slower generic /
5.38% slower consumer**, with about 8.49-8.60% more instructions. Final measured
ELF disassembly shows scalar integer/float conversions and `fmul`/`fadd`/
`fcvtms`, not a SIMD benefit. All 134 outcomes and original #299 maximum/count
statistics are unchanged. **No-go for this exact-product variant**; this does
not disprove a different whole-plane float pipeline.

## Measurement and remaining qualification

Each runtime variant is paired independently with the same control on CPU3 in
generic and consumer profiles, over 11 declared A-D cases. Every process uses
three warmups and at least 15 iterations **and** two seconds, with two reversed
fresh-process rounds. Cases include actual 16-bit input, BYPASS/VSC, tiled
layout and thumbnail overhead. No candidates are stacked.

All first-round medians reproduce from **73,998** raw samples over 264
full-protocol processes. Separate three-repeat hardware counters and final
consuming-ELF code generation are retained, never mixed with uninstrumented
timing. Every variant matches all **134** recorded outcomes: 65 full images,
12 real selected requests and 57 external conformance vectors. The seven
existing refusals preserve exact exit/error text; this is regression
qualification, not a normative conformance pass.

See [paired medians/IQRs](data/followup-paired-summary.csv),
[class changes](data/followup-class-summary.csv),
[original #299 before/after statistics](data/followup-299.csv),
[402 exact regression outcomes](data/followup-qualification.csv),
[hardware instruction summaries](data/followup-instruction-summary.csv) and
[runtime/source scope](data/followup-runtime-provenance.json).
No Go issue, merge, release change or publication has occurred.
