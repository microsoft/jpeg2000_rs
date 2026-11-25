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
including singleton and odd-origin boundaries. An actual `(3,5)`-origin encoded
full/selected probe also passes. Additional multidimensional validation is pending.
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
source-function coverage is not measured. Paired performance is pending.

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
a pass. Paired performance is pending; no adoption recommendation is made.

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
therefore do not pass. Paired performance and original #299 replay are pending.

## Measurement and remaining qualification

Each runtime variant is paired independently with the same control on CPU3 in
generic and consumer profiles, over 11 declared A-D cases. Every process uses
three warmups and at least 15 iterations **and** two seconds, with two reversed
fresh-process rounds. Cases include actual 16-bit input, BYPASS/VSC, tiled
layout and thumbnail overhead. No candidates are stacked.

Exact full/selected/conformance before/after qualification, separate hardware
counters and final code-generation evidence remain pending. The seven existing
baseline conformance refusals must stay unchanged, not be reclassified as a
pass or “fixed” by relaxing limits. No Go issue, merge, release change or
publication has occurred.
