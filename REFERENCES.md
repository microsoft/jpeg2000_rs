# Standards and implementation references

These references identify the technical basis for the decoder. They do not
grant rights to redistribute standards text, reference software, or test
vectors. The repository contains no normative PDF or purchased vector archive.

The [specification audit guide](specs/README.md) maps these reference editions
to semantic model entry points and explains variables, ranges, normalization,
rounding and checked presentation equivalences. It separates implementation
resource policies and invariant-only support from coding semantics. It does
not invent clause anchors or resolve unavailable edition text.

## Standards

| Topic | Selected reference |
|---|---|
| Core coding and JP2 | [ITU-T T.800 (2024-07)](https://www.itu.int/rec/T-REC-T.800-202407-I/en), ISO/IEC 15444-1:2024 |
| Extensions and JPX | [ITU-T T.801 (2023-08)](https://www.itu.int/rec/T-REC-T.801-202308-I/en), ISO/IEC 15444-2:2023 |
| Conformance | [ITU-T T.803 (2024-02)](https://www.itu.int/rec/T-REC-T.803-202402-I/en), ISO/IEC 15444-4:2024 |
| JPIP | [ITU-T T.808 (2026-06 catalog record)](https://www.itu.int/rec/T-REC-T.808-202606-P/en), ISO/IEC 15444-9:2026 |
| HTJ2K | [ITU-T T.814 (2019-06)](https://www.itu.int/rec/T-REC-T.814-201906-I/en), ISO/IEC 15444-15:2019 |

The separately acquired [T.801 (06/2021) publication](https://www.itu.int/rec/T-REC-T.801-202106-S/en)
was used for ADS, ATK, NLT, CBD, and reversible integer decorrelation syntax
and inverse-transform interpretation, and Annex M's single-image JPX
[routing control](validation/VALIDATION.md#single-image-jpx-routing-control).
Its SHA-256 is
`8ec28b54b53f5b6898a02d0718566600809e1c86ecbbf64ab0e1e443e7f67f40`.
This identifies the acquired reference only, not the selected 2023
consolidation; edition-difference reconciliation remains necessary.

The reversible decorrelation engineering profile uses J.3.1.1.3, Figure J.7
and the off-diagonal explanation in O.3.2. The apparent final-stage summation
index inconsistency is disclosed in
[the proof boundary](PROOFS.md#reversible-integer-decorrelation-engineering-profile).
No normative prose, diagram or PDF is included in this repository. This
interpretation is not an independent selected-2023-edition certification.

The [official third-edition summary](https://www.itu.int/dms_pubrec/itu-t/rec/t/T-REC-T.801-202308-I!!SUM-HTM-E.htm)
identifies progression-order extensions as a change from the 2021 edition.
The selected implementation supports the five Part 1 progression orders and
POC sequencing; it does not claim execution of the additional Part 2
progression-order extensions. The 2023 catalog identifies the full text as
purchase-controlled. Its public summary is not sufficient for a clause-level
reconciliation of the acquired 2021 source with the selected 2023 edition.
That comparison requires an authorized full text.

The acquired T.800 (06/2019), A.6.6, permits POC declarations across tile-part
headers, requires a tile-specific POC in that tile's first header, and assigns
each progression a zero layer start with already included packets suppressed.
Accordingly, individual header records retain range/contribution validation,
while full tile coverage is checked after all headers arrive. Per-component
resolution layer frontiers establish the complete union and declaration
novelty; physical packet traversal advances headers before exhausting an
earlier partial progression window. This is Part 1 behavior, not a claim to
implement the additional selected-2023 Part 2 progression extensions.

### JP2 primary brand and additional compatibility codes

T.800 (06/2019), I.5.2, Table I.3 and the CLi definition distinguish the
primary brand from the compatibility list. A JP2 file's required `jp2 `
compatibility code is not exclusive: advertising registered JPX compatibility
does not itself contradict a JP2 primary brand. T.801 (06/2021), M.8,
separately specifies branding for files defined by the JPX extensions.
ISO 32000-1:2008, 7.4.9, includes JP2 within the JPX formats used by JPXDecode.
These clauses justify accepting the additional compatibility codes without
waiving other container, colour, codestream or boundary checks. They do not
establish conformance of an entire PDF image or resolve the selected-edition
reconciliation identified above.
The common PDF single-codestream profile likewise retains JP2-primary files
with additional JPX compatibility codes. Announced HT in raw, JP2 or JPH form
uses ordinary decoding with strict metadata and complete framing, not legacy
damaged-input repair. The single-image JPX embedding profile follows acquired
T.801 (06/2021), M.6.2 and M.11.1: supported standard-feature masks are ORed and
must satisfy both FUAM and DCM. Flags 1, 4 and 5 identify supported Part 1
codestream functionality. Unknown required standard/vendor functionality,
composition and ambiguous codestream selection are not ignored. Broader
JPX APIs and selected-2023 edition reconciliation remain separate.

### e-sRGB is not an sRGB enumeration alias

The acquired T.800 (06/2019), I.5.3.3 and Table I.10, restrict the first
enumerated JP2 colour declaration to 16, 17 and 18. Acquired T.801 (06/2021),
M.11.7.3.1 and Table M.25, assign 20 to the JPX e-sRGB extension defined by
**PIMA 7667**, not by treating IEC 61966-2-1 sRGB samples as interchangeable.
The user-supplied [PIMA 7667:2001 copy](https://www.13thmonkey.org/documentation/fonts/pima7667-2001.pdf)
identifies the first edition, approved 2001-05-18; SHA-256
`05653ec7b3b42ad3d8b1a023dc21cfb7af69a7b8ba30c88003d20c46c40d9c20`.
Its section 4.1 and normative Annex A establish the 10/12/16-bit encoding,
offset/scale and default RGB-clipped reverse conversion. The
[issue #439 classification and implementation](validation/esrgb-classification.md)
separates that conversion from explicit, reported OpenJPEG-compatible
passthrough for the nonconforming eight-bit fixture. The copy is not
redistributed or represented as a publisher-authenticated binary. This work
does not claim reconciliation with the newer selected ITU editions.

The T.808 (06/2026) reference above identifies a catalog record, not an acquired
normative text or completed edition-difference review. Public implementation
cross-checks and JPIP regression results must not be described as a complete
normative audit of that edition.

The official conformance-asset entry point is
[ITU test signals](https://handle.itu.int/11.1002/2000/6179). Access and
redistribution conditions are independent of access to the recommendation.
Use an authorized external root as described in
[validation instructions](validation/VALIDATION.md).

## Pinned public implementation cross-checks

References without copied source are algorithm/format cross-checks, not
vendored dependencies. Preserve this distinction when adding new material.

| Project and revision | Topics and relevant paths | Relationship |
|---|---|---|
| [OpenJPEG](https://github.com/uclouvain/openjpeg/tree/8314119b067c0fc77834731168daaebd379fdb12) `8314119b...` | `src/lib/openjp2/mqc.c`, `mqc_inl.h`, `j2k.c`, `j2k.h`, `ht_dec.c`, `t1_ht_luts.h` | MQ, MCT, HT control and table cross-checks; HT VLC lookup words are derived data and retain the notices in [THIRD_PARTY_NOTICES](THIRD_PARTY_NOTICES). |
| [OpenHTJ2K](https://github.com/osamu620/OpenHTJ2K/tree/dacb452ecb21f50e88a74bf860c60f4aafa8a602) `dacb452e...` | Codestream marker/coding-unit and common type sources | DFS, ATK framing, TLM/CRG, HT capabilities, pass grouping and mixed routing; no source imported. |
| [OpenJPH](https://github.com/aous72/OpenJPH/tree/8ca3abdd3b185cd737e70c0d443171205b3e6f15) `8ca3abdd...` | `ojph_params`, `ojph_resolution`, transform and color sources, scalar CLI encoder/decoder | Directional geometry, lifting syntax, NLT and capability cross-checks; independent generated-image and fixed-stream HTJ2K comparisons; no source imported or vendored. |
| [go-jpeg2000](https://github.com/mrjoshuak/go-jpeg2000/blob/2948150e9dea47092d30895492ec1d08ae183b5c/encoder.go) `2948150e...` | `encoder.go` | Independent NLT field-framing cross-check; no source imported. |
| [CADI](https://github.com/gici-uab/cadi/tree/43314e890be4f1dde44af7853570ee874c13aac6) `43314e89...` | Main-header decoder and MCC parameter classes | MCC field-packing cross-check; reference-only, no source imported. |
| [Kakadu public sources in walls](https://github.com/wallscavesurvey/walls/tree/8428c2ba8ecde662753e4437b3f6d8ee1e783467/Kakadu6_4) `8428c2ba...` | Public API headers and JP2/JPX/client/server sources | Component DWT, JPX field and JPIP placeholder cross-checks; reference-only under upstream terms, no source imported. |
| [webjpip.js](https://github.com/MaMazav/webjpip.js/tree/f4e426de1552d4b515ebbb0531b872fc8c39edee) `f4e426de...` | Message headers, databins, tile structure, quality cache, packet collector and reconstructor | JPIP binary messages, ranges, precinct mapping and reconstruction cross-checks; no source imported. |
| [OSSIM](https://github.com/ossimlabs/ossim/blob/d4781a8c895db9bd1dd88b24f5ec498908d4f98d/src/support_data/ossimJpipMessageDecoder.cpp) `d4781a8c...` | `ossimJpipMessageDecoder.cpp` | Independent Bin-ID/VBAS/EOR cross-check; no source imported. |

## Verification tools and numerical claims

[Verus](https://github.com/verus-lang/verus) and
[Z3](https://github.com/Z3Prover/z3) are verification tools, not production
decoder dependencies. Their effective revisions are pinned by the proof
workflow. [PROOFS.md](PROOFS.md) describes the current tool boundary.

Deterministic arithmetic and successful refinement contracts do not alone
establish standards-level numerical tolerances. Independent test vectors and
oracle outputs remain necessary, especially for irreversible transforms,
color conversion, and nonlinear operations.
