# Specification audit guide

A JPEG 2000 decoder turns compressed bytes into pixels. It reads headers and
packets, recovers numerical coefficients, applies transforms, and assembles
an image. This directory describes those steps mathematically so that Verus
can check the Rust implementation against them.

If you are here to review the work, start with one small part of that pipeline.
You do not need to read the whole specification to make a useful contribution.
Keep two questions separate:

1. **Does the code do what our model says?** A successful proof answers this
   for the function and inputs covered by its contract.
2. **Does our model say what the standard requires?** That needs a separate
   comparison with the right edition of the standard.

The models and implementation were developed together, not from an
independently audited, frozen translation of the standard. Independent
model-to-standard review remains outstanding.

## Reading path and reference status

- **For orientation:** read the component map, then the short addition example.
- **For a code/proof review:** follow either example into its detailed
  walkthrough. The [technical index](../validation/normative-coverage.json)
  provides the corresponding implementation, model, contract, proof and tests.
- **For a standards audit:** choose a component and confirm the reference
  edition first. Compare its rules with the model before judging the proof.

Here is the current document basis; none of these rows means "conformance
certified."

| Selected reference | What it covers | Official free PDF | Review status |
|---|---|---|---|
| T.800 (2024-07) | Core coding and JP2 | [2019-06 (older edition)][t800-pdf] | Selected 2024 edition still needs clause-by-clause review. |
| T.801 (2023-08) | Extensions and JPX | [2021-06 (older edition)][t801-pdf] | Some interpretation used 2021; reconciliation with 2023 is pending. |
| T.808 (2026-06) | JPIP | [2022-12 (older edition)][t808-pdf] | Selected 2026 text is restricted; edition/model review is pending. |
| T.814 (2019-06) | HTJ2K | [2019-06][t814-pdf] | Text was acquired; model-to-standard review is pending. |
| T.803 (2024-02) | Conformance testing | [2024-02][t803-pdf] | A test target, not certification; official assets have separate access conditions. |

These are direct English-PDF links on ITU's site. **Older editions are not
substitutes for the selected editions:** T.800 (2024) and T.801 (2023) are
payment-controlled, and T.808 (2026) is TIES-restricted. The edition
differences have not been reconciled.

[REFERENCES.md](../REFERENCES.md#standards) has the official links and fuller
edition/support notes, including the distinction between Part 1 and Part 2
progression orders. The PDFs are not reproduced here. Access, redistribution
and automated processing are separate permissions; missing text is not a
reason to invent a citation.

## Component map

Think of the decoder as a sequence of jobs:

| Component | Its job | Start reading |
|---|---|---|
| Headers and containers | Find image data, dimensions and decoding instructions in the input bytes. | [Parsing code](../src/codestream.rs), [container code](../src/jp2.rs) |
| Packets | Work out which pieces of compressed data are present and in what order to process them. | [Packet code](../src/packet.rs), [packet models](packet.rs) |
| Coefficients and arithmetic | Recover coefficient signs and magnitudes using legacy coding or HTJ2K, without losing high bits. | [Tier-1 code](../src/tier1.rs), [integer arithmetic](../src/magnitude.rs) |
| Transforms | Undo quantization and wavelet/component transforms to rebuild sample values. | [Transform code](../src/transform.rs), [mathematical models](mod.rs) |
| Channels and color | Interpret palettes and channel mappings, then perform supported color conversions. | [Color code](../src/color.rs), [sample processing](../src/decode/output.rs) |
| Layers and frames | Combine prepared layers into output frames. | [JPX code](../src/jpx.rs), [composition models](mod.rs) |
| JPIP cache mutation | Insert owned fragments atomically, compare overlaps and normalize bytes without changing the cache on returned errors. | [Insertion code](../src/jpip/cache.rs), [complete cache-state model](jpip_cache_insert.rs) |
| JPIP public layouts | Validate caller codestream/container layouts and derive complete reconstructed bytes or the first error from the actual cache. | [Reconstruction code](../src/jpip/reconstruction.rs), [complete layout models](jpip_layout.rs) |
| JPIP responses | Parse raw responses, insert actual fragments, and retain exact earlier commits and summary/error fields. | [Ingestion code](../src/jpip/message.rs), [complete response model](jpip_response.rs) |
| JPIP ranges and packet bytes | Derive ordered missing intervals, exact work/error frontiers and original packet byte slices from the physical cache. | [Range code](../src/jpip/ranges.rs), [complete range/read models](jpip_ranges.rs) |
| JPIP owned plans | Build actual layer boundaries and reconstruct caller-planned packet reports and optional exact bytes from physical plans and cache. | [Plan code](../src/jpip/precinct.rs), [complete plan/reconstruction models](jpip_planned_packets.rs) |
| JPIP transcode | Derive complete header availability, in-place layer patches and first-error frames, exact Psot/owned output bytes and genuine final raw-layout validation. | [Transcode code](../src/jpip/precinct.rs), [complete transcode models](jpip_transcode.rs) |
| Caller-planned JPIP progression | Derive complete full/selected typed-image updates and final decoder state from physical cache/plan inputs, retaining earlier state on returned errors and skipping unneeded decoding. | [Progressive code](../src/jpip/progression.rs), [complete progressive models](jpip_progressive.rs) |
| Automatic JPIP main-header normalization | Derive the raw-input byte/error Result with exact ordered primitive-call requests and observed reservation outcomes; physical allocator internals and complete automatic images remain separate. | [Header code](../src/jpip/automatic_headers.rs), [ordered request/normalization model](jpip_normalization.rs) |
| Raw JPIP tile transitions | Derive every stored transition/header field and complete cache-report availability, semantic needs and missing ranges through original word/marker/PLT/SOT/SOD traversals. | [Transition code](../src/jpip/mapping.rs), [complete transition/report models](jpip_transitions.rs) |

This is a map of responsibilities, not a claim that one theorem connects the
entire pipeline. The [detailed component index](AUDIT_REFERENCE.md#component-entry-points-and-boundaries)
lists the exact model names and local limits. [PROOFS.md](../PROOFS.md)
explains what inputs each checked stage starts from and where the remaining
connections are.

## Example 1: full-width magnitude addition

**Question to audit:** can an addition silently lose its high bits?

Start with `Magnitude::checked_add` in [the Rust code](../src/magnitude.rs).
A magnitude is stored as six 64-bit words. Its contract must describe the
value of the whole number, not just the first word: return the exact sum when
it fits, or the specified overflow error otherwise.

Compare that promise with the [addition model](mod.rs), then inspect the carry
proof and the independent bit-by-bit reference test. The
[full walkthrough](AUDIT_REFERENCE.md#worked-example-1-full-width-magnitude-addition)
names every definition and test to follow. This is a review of arithmetic;
it does not establish how compressed bits became those numbers.

## Example 2: PLM packet-length admission

**Question to audit:** what changes when parsing fails partway through?

A PLM marker carries encoded packet-length information. Start with
`Parser::parse_plm` in [packet-header parsing](../src/codestream/packet_headers.rs), then compare it
with the [packet-length models](mod.rs).

Do not check only the successful result. For example, a group is appended
before the tile-part limit is checked. If that check fails, the model and
contract must both retain the appended group. The
[full walkthrough](AUDIT_REFERENCE.md#worked-example-2-plm-packet-length-admission)
traces the bytes, counters, error offsets, proof and tests. It shows a local
parser guarantee, not a proof of the complete public decoder.

Both examples explain code-to-model review. A completed standards audit also
needs the independent source comparison described above.

## Three kinds of material

When opening a definition, ask which of these it is:

- **A rule intended to represent the standard:** for example, what an encoded
  field means. Its correspondence with the source text needs auditing.
- **A choice made by this implementation:** for example, integer capacity,
  fixed-point rounding, supported profiles, 16-bit layer composition or a
  resource limit. Do not mistake such a choice for a standard requirement.
- **A tool for a proof:** algebra, representations and loop bookkeeping in
  [proofs/](../proofs/) and [internal_specs.rs](../proofs/internal_specs.rs).
  These help establish a result; they are not additional codec rules.

## What is established, and what is not

Cargo and Verus use the same [executable Rust](../src/lib.rs), not separate
decoders. Contracts check specified results, errors and state changes.
But the starting point matters: a proof that begins with supplied coefficients
does not prove that earlier compressed-byte decoding was correct.

We do not claim a completed independent standards audit, a complete public
bytes-to-image proof, official conformance or release authorization.
Generated tests and comparisons with other decoders are useful checks, not
certification. See the [concrete proof boundaries](../PROOFS.md#concrete-contract-boundaries)
and [validation guidance](../validation/VALIDATION.md).

Function counts are not a completeness percentage; the
[proof-report format](../validation/proof-coverage.schema.json) records source
function coverage as not measured. The released verifier also disables Verus
lifetime analysis (`--no-lifetime`); ordinary Rust borrow checking still runs.
See the [tool limitation](../PROOFS.md#current-lifetime-analysis-limitation)
and [verification instructions](../PROOFS.md#reproduce-verification).

## Reconstruction reading path

To follow coefficients through to sample values, use the
[reconstruction tour](AUDIT_REFERENCE.md#reconstruction-reading-path).
At each step, note which inputs are supplied and which the code actually
derives. The [bounded reconstruction notes](../PROOFS.md#bounded-supplied-coefficient-reconstruction)
and [buffer-composition notes](../PROOFS.md#complete-wavelet-stage-and-real-owner-buffer-mct-composition)
explain those distinctions in detail.

<a id="frozen-f5h-directional-reader-stages"></a>
## HTJ2K bit readers

For a lower-level audit, start with the
[bit-reader explanation](AUDIT_REFERENCE.md#ht-directional-reader-contracts),
then the [refinement](AUDIT_REFERENCE.md#frozen-full-f5h-refinement-plane-profile)
and [cleanup](AUDIT_REFERENCE.md#frozen-f5h-cleanup-plane-reconstruction-profile)
details. Reader proofs alone do not establish the complete coefficient
decoder. Labels such as "F5H" in that reference are internal work labels,
not names from the standard.

[t800-pdf]: https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-T.800-201906-S!!PDF-E&type=items
[t801-pdf]: https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-T.801-202106-S!!PDF-E&type=items
[t808-pdf]: https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-T.808-202212-S!!PDF-E&type=items
[t814-pdf]: https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-T.814-201906-I!!PDF-E&type=items
[t803-pdf]: https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-T.803-202402-I!!PDF-E&type=items
