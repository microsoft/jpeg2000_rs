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
and inverse-transform interpretation.
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
