# Supported decoder profiles

This document describes implementation scope, not certification. JPEG 2000 is
the ISO/IEC 15444 and corresponding ITU-T T.8xx standards family. It is not a
single RFC, and this library does not implement every part of that family.

## Conformance claim and evidence matrix

The scope below freezes the implementation families being qualified; it does
not declare them conformant. The selected editions are listed at the end of
this document. Resource and numeric policies, deliberate exclusions and
unqualified combinations below remain part of the scope. A failed comparison
must not be hidden by silently narrowing the claim or changing a tolerance.

Keep four evidence levels separate:

1. **Implemented:** a real supported execution path exists.
2. **Independently qualified:** the stated finite profile passed an independent
   expected-result or decoder comparison.
3. **Normatively reviewed:** independent review established correspondence to
   an authorized exact edition and frozen requirements.
4. **Officially tested:** the applicable, rights-cleared conformance selection
   passed with independently established expected outcomes.

No family currently has completed levels 3 or 4. Successful Verus checks apply
to the expressed contracts, not to an independently frozen translation of the
standard. The [technical reference inventory](validation/normative-coverage.json)
maps named implementation/model/contract/proof/test entries; it is not an
exhaustive standards-clause or source-function-coverage measurement.

Ordinary JP2 full/selected typed and colour decoding displays the first
codestream, ignoring later codestream contents while retaining all-box framing
and resource limits. Explicit `jp2::parse_and_inspect` still inspects every
codestream. JPX selection/count and JPH singleton policies are unchanged.
The pinned Glymur 0.13.8 first-display comparison preserves its warning about
ignored later codestreams; it does not certify full container conformance.

| Qualification family | Actual entry and inventory examples | Existing independent evidence | Remaining claim boundary |
|---|---|---|---|
| Part 1 raw headers, tile state and JP2 input | [Parser](src/codestream/layout.rs), [public raw APIs](src/decode/api.rs); `part1-complete-native-codestream-reader`, `part1-complete-native-raw-coding-style` | Generated framing/error tests and selected reference-coded inputs | Whole raw header/inherited-tile-to-layout result and public composition |
| Part 1 legacy entropy and packets | [Tier-1](src/tier1.rs), [packets](src/packet.rs); `part1-complete-legacy-tier1` | Selected MQ/RAW, style, ROI, layer and selection profiles | Independent rule correspondence and unqualified combinations |
| Part 1 transforms and typed output | [Transforms](src/transform.rs), [typed output](src/image.rs); `part1-reversible-five-three`, `part1-irreversible-numerical-model` | Exact selected reversible comparisons; explicit engineering lossy budgets | Full implemented precision/component range and prescribed conformance tolerances |
| Part 2 extensions, color and JPX | [Component transforms](src/image/mct.rs), [JPX rendering](src/jpx/render.rs); `part2-jpx-general-layer-rendering`, `part2-jpx-composition-rendering` | Selected raw numeric properties, native-plane and independent rational composition expectations | Actual source-to-normalization/frame joins, native JPX oracle gaps and edition reconciliation |
| Part 9 non-network JPIP | [Messages and reconstruction](src/jpip.rs); `part9-codestream-reconstruction`, `part9-progressive-updates` | Selected framing, fragment, reconstruction and progressive relations | Exact selected-edition correspondence and applicable official cases |
| Part 15 HTJ2K and mixed routing | [HT cleanup](src/tier1/ht_cleanup.rs), [retained contributions](src/packet/contributions.rs); `part15-complete-actual-cleanup-plane`, `part15-mixed-routing` | Selected pinned scalar OpenJPH and mixed-route comparisons | Broader precision/component/profile combinations and independent normative review |

These are entry points, not substitutes for the complete per-family profiles
and limitations below. In particular, ICC execution, additional Part 2
progression orders, arbitrary native JPX semantics and every combination of
the implemented 1..38-bit range are not qualified by the current comparisons.
Encoding and network/application services are not decoder conformance claims.

The remaining work is tracked under
[#132](https://github.com/microsoft/jpeg2000_rs/issues/132):
[#186](https://github.com/microsoft/jpeg2000_rs/issues/186) for this scope/matrix,
[#187](https://github.com/microsoft/jpeg2000_rs/issues/187) for independent
model correspondence, [#188](https://github.com/microsoft/jpeg2000_rs/issues/188)
for official vectors, [#189](https://github.com/microsoft/jpeg2000_rs/issues/189)
for verification assurance and
[#190](https://github.com/microsoft/jpeg2000_rs/issues/190) for resource/fuzz
qualification. Actual proof dependencies remain
[#133](https://github.com/microsoft/jpeg2000_rs/issues/133) ->
[#134](https://github.com/microsoft/jpeg2000_rs/issues/134) ->
[#131](https://github.com/microsoft/jpeg2000_rs/issues/131) ->
[#130](https://github.com/microsoft/jpeg2000_rs/issues/130).
None of these engineering trackers clears the document-use decisions in
[#149](https://github.com/microsoft/jpeg2000_rs/issues/149).

## Inputs and outputs

| Interface | Behavior |
|---|---|
| Raw codestream | Component decoding and metadata inspection |
| JP2 | Container validation, typed component output, palette/channel mapping, and explicit color conversion |
| JPH | Branding/capability inspection and legacy/HT/mixed component decoding |
| JPX | Explicit indexed codestream, layer, composition, and frame APIs; no implicit first-codestream selection |
| JPIP | Binary messages, sparse databins, range/completeness status, reconstructed decoder inputs, and progressive updates |

Output retains component precision and signedness, image origins, subsampling,
and channel association metadata. Component sample output and converted color
output are distinct interfaces.
Selected color conversion preserves the full-image sampling phase at the
requested native DWT resolution, including regions starting between component
samples. It may decode bounded left/top context from neighboring tiles before
cropping the converted output; resource limits include that context. Component
selection continues to return the requested native component grids.
Tile-local nonlinear point transforms are applied on those native grids:
discarded DWT levels reduce tile-component bounds before output clipping,
including selected raw codestream, JP2 and JPX decoding. Tile and cropped
requests retain the transform of each contributing source tile.
The retained-assertion engineering profile preserves NLT header scope:
tile-specific, tile-default, main-specific, then main-default. Local defaults
do not erase local specifics or the inherited fallback descriptors.
LUT transforms normalize the complete unsigned source rank by `(2^B)-1`,
including both endpoints; signed source samples retain their half-range offset.
This retained-assertion behavior does not assert agreement with conflicting
public scalar-normalization implementations.
Empty half-open resolution axes have zero code-block and precinct cells,
including nonaligned endpoints. Fully clipped empty subbands produce no
execution; empty resolutions do not introduce phantom precinct databin IDs.
JPIP VBAS fields accept value-equivalent leading-zero groups within the
existing ten-byte and unsigned 64-bit bounds. Physical header lengths and
field terminators are retained; overflow and truncated fields remain errors.
Container parsing requires one initial signature and file-type prefix.
Later top-level repetitions are malformed, including after a codestream;
unknown opaque payloads are not scanned for embedded prefix bytes.
CDEF metadata distinguishes physical channel indices from colour associations.
Raw record parsing bounds the physical index, retains colour-index metadata
independently, and preserves repeated descriptions and the whole-image and
unassociated sentinels. Colour interpretation is a separate consumer step.
Once a header colour specification is selected, later COLR boxes retain
framing, resource accounting and common-prefix validation but do not replace
the selection or trigger irrelevant colour/ICC interpretation. Associated
headers apply the same rule after their first provided colour override.

## Coding features

The implementation contains:

- Multiple tiles, components, tile parts, and quality layers.
- Signed/unsigned components with nominal precision from 1 to 38 bits.
- LRCP, RLCP, RPCL, PCRL, and CPRL progression and POC windows.
- Precincts, inclusion/zero-bitplane tag trees, coding-pass and segment lengths.
- Main/tile COD, COC, QCD, QCC, and RGN state and precedence.
  Main-header QCD may precede COD; its quantization parameters are validated
  once the coding style is available, matching tile-header handling.
  Ordinary COD/COC precinct axes must be nonzero above resolution zero.
  Resolution-zero zero exponents remain supported; explicit Part 2
  decomposition selectors retain their separate deferred admission.
- PLM/PLT packet lengths, PPM/PPT packed headers, SOP/EPH, and TLM checks.
  The retained-assertion engineering profile uses one-byte PLM group counts
  and allows groups to continue across PLM markers at complete packet-length
  codewords. An unfinished final group is rejected at its originating marker.
  PLM and PLT may coexist only when their complete packet lists agree.
  When SOP use is enabled, individual packets may omit SOP. Present markers
  retain their length and caller-specific sequence validation; inline and
  packed-header accounting follows the bytes actually present.
  Packet headers ending in FF consume the required stuffed byte before EPH
  and body accounting, with byte limits and stuffing errors checked first.
- The five Part 1 progression orders and POC sequencing, not additional Part 2
  progression-order extensions.
- Legacy MQ and raw-bypass Tier-1 passes, coding-style routing, and Maxshift undo.
- HT cleanup, significance propagation, magnitude refinement, placeholder and
  replacement pass sets, and mixed legacy/HT routing.
- Reversible 5/3 and fixed-point irreversible 9/7 synthesis.
- Part 2 MCT/MCC/MCO transforms and segmented records; directional/general
  decomposition and kernel metadata via DFS/ADS/ATK; CRG, NLT, and CBD handling.
  ATK half-filter taps retain absolute low/high band phase on odd-origin axes.
  Its Q32 arithmetic preserves exact signed unit scaling and rounds nearest
  with ties away from zero, subject to checked range and shift limits.

Every feature is subject to resource, geometry, numeric-range, and profile
validation. A list of implemented code paths is not an independent proof that
every normative requirement of their standard editions is represented.
The independent generated legacy numerical suite covers selected signed
1/2/4/7/8/9/12/16/17/24-bit monochrome profiles and unsigned
1/2/4/7/8/12/16/20/24-bit profiles. Selected signed/unsigned 25-bit cases are
qualified only at zero DWT decomposition, including tiled, layered and JP2
variants. Its RGB cases remain unsigned 8/16-bit. This evidence does not qualify the
entire implemented 1..38-bit range. See [validation](validation/VALIDATION.md)
for exact cases, metadata checks, reference-roundtrip guards and limitations.
The legacy RGB16 cases explicitly check enabled/disabled component transforms
with exact reversible output, plus enabled-transform irreversible output with
maximum error 8 and per-component RMSE 2.0. The latter budget is applied to both
the original/reference prequalification and reference/subject comparison.
Independent fixtures also check selected component-wide Maxshift upshifts and
binary-complement NLT type 3 on finite IEEE binary32 bit patterns, including
negative zero. The latter checks exact integer bit representations, not a
floating-point image API or arbitrary 32-bit pixel/color conformance.
Selected live HT RGB16 profiles also qualify enabled/disabled component
transforms, sparse/multi-code-block images, tiled nonzero origins and JPH,
with exact lossless planes and explicit engineering budgets for irreversible
output. These do not qualify every higher-precision multicomponent profile.
Additional full-range HT monochrome profiles cover signed/unsigned
25/26/28/31-bit integers at exactly two DWT decomposition levels, with exact
original/reference and reference/subject equality. Their canonical PGX originals
are transported as little-endian native RAW samples to the pinned scalar
OpenJPH tools; source, encoder input, codestream and tool hashes are recorded.
The runner validates actual SIZ geometry, component count, precision, signedness
and sampling, and COD decomposition, wavelet and explicitly requested component
transform settings before numerical comparison.

These additions came from a finite 44-candidate precision/component
qualification matrix, including zero/two-level DWT, 25/26/28/31-bit full-range
monochrome, selected higher-precision RGB and fixed irreversible budgets.
Thirteen candidates qualified, including two existing 25-bit zero-DWT legacy
controls; eleven add regression coverage. The other 31 remain unqualified
reference paths, not subject defects, passing cases or skipped qualification
tests. In particular, legacy 25-bit DWT and higher full-range precision,
HT zero-DWT at these precisions, and selected RGB17/RGB24 paths remain outside
this independent evidence. No thresholds were relaxed to admit them.
This is not completion of broader precision/component qualification: those
reference gaps remain open, and local measurements do not replace exact-candidate
three-OS evidence or the remaining integration/publication gates.

Broader selected-profile qualification retains fourteen additional qualified
profiles from a predeclared twenty-candidate matrix: component-wide Maxshift
on 20-bit grayscale and independently coded RGB16, a fixed-budget irreversible
gray16 Maxshift case, tiled/layered RGB16 with all legacy coding-style flags,
independent native-resolution sRGB/sYCC expectations,
gray/global-alpha straight and premultiplied containers/composition, and
nonzero mixed legacy/HT tiles in raw/JPH. Full/region/tile/native-resolution
checks use independently decoded native planes, never subject full-image
output as expected pixels. Color normalization and source-over expectations
use wide rational arithmetic without calling the decoder's color/composition
implementation. Exactness and fixed engineering budgets are detailed in
[validation](validation/VALIDATION.md).

The selected 47x35 RGB16, origin (3,5), 16x16-tile, three-layer
`-r 8,3,1 -M 63 -mct 1` legacy profile now requires exact independent
original/reference/subject output and full/region/tile/native-resolution
selections. This does **not** qualify every combination of coding styles,
quality layers and tiles. Selected signed12 Maxshift/layers and RGB8
irreversible layer candidates fail original/reference
budgets, and two selected three-layer prefixes are degenerate. They are not
passing or skipped qualification tests. Independent native JPX frame rendering
and ICC execution remain unavailable/excluded; selected rational composition
fixtures do not qualify arbitrary native container semantics.

## Containers, color, and JPIP

JP2 supports component bit depths, palette mappings, channel definitions,
resolution metadata, and ICC profile retention. Color execution is pinned to
enumerated values 16 (sRGB), 17 (grayscale), and 18 (sYCC), including signed,
subsampled, and origin-aware channels and alpha handling.
Palette boxes admit 1 through 1,024 entries and retain up to 255 columns;
an out-of-domain entry count is rejected before descriptor/table interpretation.

JPH component APIs retain typed planes when `colr` is absent and IHDR declares
`UnkC=1`. `ColorMethod::Unspecified` represents that absence explicitly; it is
not an enumerated colour value or an invented `colr` box. Its precedence and
approximation placeholders are zero and its ICC profile is absent. Colour-channel
claims without specified colour are rejected. Explicit colour conversion reports
`UnsupportedColorConversion::UnspecifiedColorSpace` rather than inferring RGB or
grayscale. JP2/JPX and `UnkC=0` retain their required-colour checks.

JPX exposes codestream/header association, layer registration, channel
association, opacity, composition instructions, timing, and indexed frame
rendering. Rendering is bounded and deterministic; it does not provide a
wall-clock animation player or interpret arbitrary application metadata.
Single-layer output retains its straight/premultiplied color samples and the
corresponding alpha flag, consistent with color conversion. Composition/frame
output is straight alpha, with transparent composed pixels represented as
transparent black. Selected global-alpha RGBA profiles are checked against
an exact rational source-over oracle; this is not colorimetric certification.

JPIP supports checked binary message headers and VBAS fields, out-of-order
fragments, duplicate/overlap consistency, final-length/completeness queries,
metadata placeholders, precinct mapping, packet reconstruction, and
transactional progressive decode. Availability and missing-range results
distinguish incomplete data from successful reconstruction.

Semantic data-bin classes are 0, 1, 2, 4, 5, 6 and 8. Raw class IDs 3 and 7
remain parseable, including their auxiliary fields and header history, but are
reported as `Unassigned` and rejected by cache insertion. Only classes 0/1
and 4/5 share data-bin identity.
Metadata class 8 is target-wide: CSn is retained in parsed headers and getters
but does not partition metadata cache identity. Other classes remain
codestream-scoped. This engineering behavior follows the user-approved retained
Sarah assertions; independent selected-edition correspondence remains separate.

Equivalent metadata replacement retains its declared equivalent box type and
short/extended header together with its payload. When original contents are
selected first, their original header remains authoritative. This does not
change metadata-bin scope, codestream-placeholder or NCS admission policies.

An inherited Class or CSn with no previous data-message value defaults
independently to zero. Header-context getters still report `None` until a
complete data message commits history; errors and EOR do not commit it.
A persistent parser retains its history, but each response ingestion starts
fresh even when its cache already contains databins.

For retained SOT headers, a nonzero `Psot` must cover the complete retained
header. An undersized declaration returns `InvalidTilePart` at the tile-part
start; it is not an unknown-length transition. The final zero-`Psot` form and
header-only bins without an SOT retain their unknown-length representation.
Complete SOT-free tile-header bins may omit SOD. Automatic reconstruction
normalizes either form to one final SOD; absent or incomplete bins are still
unavailable, and bytes following SOD remain invalid.

Explicit `JpipPrecinctCodestreamPlan` transcodes are restricted to a single
tile-part with LRCP progression, inline packet headers, and no POC, PLT, or PPT
in the reconstructed input. Both the main and effective tile coding styles
must use LRCP, including tile COD overrides. The plans require already-reframed
headers; original packet-length declarations must not be copied into a shortened
quality prefix. Automatic reconstruction performs its own header normalization.

### Retained-assertion engineering requirements

The user-approved Sarah acceptance profile additionally requires:

- A nonempty JPX codestream-header sequence has one header per codestream.
- Association boxes contain at least two immediate children.
- Explicit compositing-layer registration is present in every layer or none.
- A nonpersistent, zero-life instruction has no rendering action; layer
  assignment and reuse scheduling remain accounted.
- Single-stream placeholders may carry an optional NCS word, consumed without
  changing their stream count of one. Multistream NCS remains required/nonzero.

These are intentional engineering behavior changes. Retained assertions,
contrary public-reference observations and independent selected-edition
correspondence remain separate; this profile does not assert standards closure.

## Selection

Selected APIs accept a tile index or a unique rectangular tile set, an absolute
image-reference-grid region, and a native resolution reduction. They validate
component origins/subsampling and skip unnecessary tiles or high-resolution
bodies before Tier-1. Packet framing that must be parsed is still accounted
as input/work.

## Deliberate exclusions

- Encoding.
- JPEG 2000 parts other than the selected decoder families below.
- Network transport, HTTP client/server behavior, TLS, authentication, request
  scheduling, and JPIP cache-model signaling syntax.
- An ICC color-management engine. Profiles are retained without execution.
- Implicit execution of unknown enumerated color spaces or external
  profile-number registry values.
- Arbitrary semantic interpretation of XML, UUID, and application metadata.
- General streaming incremental decoder state and internal parallelism.

Unsupported capabilities remain typed errors. Reserved fields, contradictory
signaling, and malformed structures are not accepted as supported extensions.

## Selected standards and traceability limits

| Part | Reference edition | Scope |
|---|---|---|
| 1 | ISO/IEC 15444-1:2024 / ITU-T T.800 (2024-07) | Core codestream and JP2 |
| 2 | ISO/IEC 15444-2:2023 / ITU-T T.801 (2023-08) | Codestream extensions and JPX |
| 4 | ISO/IEC 15444-4:2024 / ITU-T T.803 (2024-02) | Conformance validation target |
| 9 | ISO/IEC 15444-9:2026 / ITU-T T.808 (2026-06 catalog record) | Selected non-network JPIP behavior |
| 15 | ISO/IEC 15444-15:2019 / ITU-T T.814 (2019-06) | HTJ2K |

Part 2 implementation references include the separately acquired T.801
06/2021 text. That source is not a byte-for-byte record of the selected
08/2023 consolidation; reconciling edition differences remains a traceability
requirement. Confirm the final Part 9 publication record before claiming
edition-level conformance.

Official Part 4 assets are not bundled. Passing unit tests, generated fixtures,
or Verus does not establish official conformance. Fixed-point numerical models
need independently measured tolerances for lossy output.

See [references](REFERENCES.md), [proof boundaries](PROOFS.md), and
[validation instructions](validation/VALIDATION.md).
