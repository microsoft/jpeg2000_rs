# jpeg2000-decoder

A resource-bounded JPEG 2000 decoder written in Rust, with Verus specifications
and proofs attached to the production implementation.

The Cargo package is `jpeg2000-decoder`; Rust code imports it as
`jpeg2000_decoder`. The repository remains
[`microsoft/jpeg2000_rs`](https://github.com/microsoft/jpeg2000_rs).
Experimental maintenance [version 0.1.1](https://crates.io/crates/jpeg2000-decoder/0.1.1)
is published. This branch is **unpublished 0.3 development**; the experimental
0.2 release line is maintained separately on `release/0.2`. The PDF recovery,
centered-output, deadline, MQ and buffered incremental APIs are not part of the
bounded 0.1.1 maintenance release. Registry publication remains disabled here;
every release requires separate exact-candidate authorization and qualification.

The library decodes raw codestreams and JP2/JPH containers, provides explicit
JPX codestream and frame selection, and supports bounded JPIP databin
reconstruction. It returns typed sample planes without discarding component
precision, signedness, origins, or subsampling.

JPH component decoding accepts an omitted `colr` box when `UnkC=1`, without
guessing a colour space. Its header reports `ColorMethod::Unspecified`; explicit
colour conversion returns `UnsupportedColorConversion::UnspecifiedColorSpace`.
These development API variants must be handled by exhaustive colour-method
matches. Ordinary JP2/JPX header parsing still requires colour metadata.

JP2 decoding displays the first codestream and ignores the contents of later
codestream boxes. Container framing and resource limits still apply to every
box. The explicit `jp2::parse_and_inspect` API inspects every codestream instead;
JPX selection and JPH singleton policies are unchanged.

This is experimental software, not a certified JPEG 2000 implementation.
Official conformance testing and broader independent validation are required
before making a standards-conformance claim.

## Build

Install [rustup](https://rustup.rs/), then run:

```sh
cargo build --locked
cargo test --all-targets --locked
```

Ordinary decoder builds support Rust 1.88.0 and newer. CI checks this minimum
with `cargo +1.88.0`; the development toolchain remains pinned separately in
[rust-toolchain.toml](rust-toolchain.toml).
The default decoder build has no external Cargo dependencies and forbids unsafe
code. The optional `verus` feature enables the pinned verification library;
it does not install or run the verifier. That feature is outside the runtime
minimum-version guarantee and uses its own toolchain.
See the [Cargo-Verus instructions](PROOFS.md#reproduce-verification).
Package publication from the development branch is disabled.

## Use with the image crate

The experimental [`jpeg2000-image` companion](adapters/image/README.md)
implements `image::ImageDecoder` and opt-in `ImageReader` hooks. It provides
normalized U16 grayscale/RGB output, straight whole-image alpha, and explicit
color policy for raw codestreams. Its narrower supported profile, input caps,
memory-accounting limitations and unsupported cases are documented separately.

It is a separate workspace package, not a decoder feature or part of the
decoder's verification claim. Root Cargo commands still select only the
decoder by default; build the adapter with `cargo test -p jpeg2000-image --locked`.
The companion keeps publication disabled and does not replace the standalone
packaged-decoder consumer gate.

## Decode a JP2 image

```no_run
use jpeg2000_decoder::{DecodeOptions, TypedSamples, decode_jp2};

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let input = std::fs::read("image.jp2")?;
let image = decode_jp2(&input, &DecodeOptions::default())?;

for component in image.components() {
    let info = component.info();
    match component.samples() {
        TypedSamples::Signed(samples) => {
            println!("{}-bit signed component: {} samples", info.precision, samples.len());
        }
        TypedSamples::Unsigned(samples) => {
            println!("{}-bit unsigned component: {} samples", info.precision, samples.len());
        }
    }
}
# Ok(())
# }
```

Use `decode_codestream` for a raw codestream, `decode_jph` for JPH, and
`decode_jpx_codestream` with an explicit index for JPX. Color-conversion and
JPX layer/frame APIs are separate from component sample decoding; see the
[public exports](src/lib.rs).

For interpolation before final rounding/clipping, use
`decode_codestream_reconstructed` for raw input or `decode_jp2_reconstructed`
for a JP2 container. Both return centered `i64` component planes with
`fraction_bits` and the genuine component grid. JP2 framing, profile and
header consistency remain checked. NLT and JP2 palette/channel processing are
explicitly rejected rather than silently bypassed; color metadata does not
convert these samples. These are strict APIs, not incremental-input or
damage-recovery modes.

For tile, region or reduced-resolution requests, the corresponding strict
`decode_codestream_reconstructed_selected` and `decode_jp2_reconstructed_selected`
APIs take a `DecodeSelection`. They preserve the same centered samples and
metadata restrictions, and never automatically recover an incomplete canvas.

### Opt-in incremental raw/JP2 input (buffered/replay)

Enable `incremental-input` and use `incremental::IncrementalDecoder::new`
with an `IncrementalFormat`, immutable options and selection. `feed` appends;
`feed_at` also accepts sparse, out-of-order input and identical overlap.
Conflicting overlap reports its exact byte offset without changing retained
bytes. Feeding never runs the codec. Progress reports consumed/retained source,
gaps, committed bytes, decode attempts, replay bytes and wrapper work.

Request a typed `decode` or centered `decode_reconstructed` preview explicitly.
`NeedMoreData` publishes nothing; `Preview` is provisional, never completion.
An incomplete packet does not replace the committed output. Partial previews
support one inline tile/part without length or packed-header tables; other
layouts report `PreviewUnavailable` until ordinary decoding is possible.
Snapshots report synthetic EOC and rewritten tile-part/container lengths;
original bytes, including received JP2 footers, remain unchanged.

Call `finish` (or `finish_at`) **only at actual EOF**. It seals input; unresolved
gaps then produce `Truncated`, not an indefinite wait. The first final call
decodes the exact original input with the ordinary selected API, including its
full geometry, metadata and centered-headroom rules. Strict EOF failures stay
errors. Only the separately named `new_pdf_compatible` constructor requests
the existing common PDF recovery policies, and only after EOF.

This initial implementation buffers and replays, **not saved entropy state**.
Each new eligible snapshot/final request invokes the single existing decoder;
repeated same-prefix calls return `Unchanged` without decoding/copying an image.
Retain the previous image separately for each output mode. Avoid polling after
every byte when previews are unnecessary: feed small chunks and decode at EOF.
Contiguous feed is linear; sparse updates stage retained data and can be
quadratic. Wrapper work is cumulatively capped, but backend work/output limits
remain stage-local, not a global CPU or live-memory bound. Allocation refusal
preserves input for retry while attempted work stays charged. With deadlines,
`with_deadline` only sets/tightens the absolute deadline; expiry cancels the
object permanently, including ambient-scope and publication-exit expiry.

The feature is off by default and outside pinned Verus qualification; combined
proof/profile builds fail explicitly. See [profiles](SUPPORTED.md) and
[incremental validation](validation/VALIDATION.md#incremental-input-profile).

### Opt-in cooperative deadlines (native-only profile)

Enable the `cooperative-deadlines` Cargo feature to export
`with_decode_deadline(Instant, operation)` and `DecodeError::DeadlineExceeded`.
The caller supplies the absolute deadline; no global timeout is selected.
Nested scopes use the earliest deadline. Entry and exit are checked, including
an error return; expiry at the exit checkpoint takes precedence. Prior
thread-local state is restored on returns and native Rust unwinding.

Checks occur before/after managed reservations and bulk operations, at parser,
box, packet, tile/component and coding-pass/stripe stages, and periodically in
named sample loops. This is cooperative cancellation, not hard preemption,
cross-thread cancellation or a saved decoder continuation. Native allocators,
opaque bulk/host operations and uninstrumented intervals cannot be interrupted.
Low-level mutable objects may already be changed on cancellation; use a fresh
decode rather than treating expiry as a resumable state.

**Qualification boundary:** real clock/TLS effects are native-tested, not
covered by the pinned Verus profile. The feature is off by default. Existing
default decoder contracts and verification flags are unchanged; trying to
verify with this feature enabled fails explicitly rather than silently erasing
checks or weakening models. See [profiles](SUPPORTED.md) and
[checkpoint observations](validation/VALIDATION.md#cooperative-deadline-profile).

### Explicit raw missing-EOC recovery

`decode_codestream_recover_missing_eoc(input, options)` is a separate opt-in
API. It can append only `FF D9` to the documented sole image tile / sole
open-ended (`Psot=0`, part index zero, count zero or one) tile part after checked
structural framing. One ordinary strict decode must then succeed; incomplete
headers/packets, genuine entropy errors, finite-Psot EOC loss, other parts/tiles,
and existing-EOC-plus-trailer inputs are not repaired. No bytes are discarded.
Intact inputs use ordinary strict decoding without a repair copy.

The result contains the typed image and a non-exhaustive report stating whether
EOC was appended, original/effective sizes, actual width/height/origin and the
additional preflight/copy accounting. The extra stage jointly respects the
existing work cap; strict decode retains its existing **separate stage-local
counters**, not a new global counter. A repair uses one fallible reservation
and exactly input length plus two logical bytes. Std physical reservation and
native refusal/unwind tests are not mathematical allocator/unwind proofs.

This is a bounded raw-only W09 increment, **not completion of W09/#291**:
W06/#287's full fallible surface, W07/#289's cooperative deadline API/scope and
the remaining #300 integration obligations are still open. No deadline exists
in this API. Container dimensions, absent tiles, MQ damage, trailers and
reconstruction output remain separate W10/W11/W15/W18/W19 work.

### Explicit JP2 dimension recovery

`decode_jp2_recover_dimensions(input, options)` accepts contradictory container
width/height only, using the genuine SIZ canvas and component grid. Its result
contains the typed image and a report with `ignored_container_dimensions`,
original header dimensions and actual canvas dimensions/origins. No pixels are
added to fill the contradictory declaration; ordinary `decode_jp2` stays strict.

`inspect_jp2_recover_dimensions` returns parsed file/codestream metadata and the
same report, not a decoded-image promise. Entropy errors and missing tiles can
still make decoding fail. `decode_jp2_reconstructed_recover_dimensions` preserves
centered fractional samples for interpolation, with the same explicit NLT and
palette/channel restrictions as strict reconstruction output.

Component counts and precision/sign must still match, including every variable
BPCC declaration and inherited/overridden associated headers. Existing framing,
profile and resource checks remain, including limits on declared metadata.
These APIs have no global recovery toggle, copy, retry or automatic EOC repair.
They do not supply the separate deadline, absent-tile, MQ or trailer policies.

### Common PDF recovery and inspection

`decode_pdf_compatible(input, options, selection)` and
`decode_pdf_reconstructed(input, options, selection)` compose the implemented
policies in one explicit call for raw input or a single-codestream Part1 JP2:
bounded missing-EOC repair, SIZ dimension authority, genuine sole-present-tile
selection, cumulative terminal-trailer admission and complete off-by-one
tile-part-count correction. JP2-primary fallback files
may advertise additional JPX compatibility. Non-JP2-primary JPX/JPH containers
and Part15 codestreams remain outside this facade; use their explicit APIs.

The result carries `PdfRecovery` flags, exact trailer bytes, original/effective
**codestream** byte counts, preflight/copy accounting and any full intended-canvas
sample bound. Whole JP2 input limits are still enforced. A repair makes one
fallible raw-codestream copy of length plus two after the accepted structural
preflight. The only boundary retries are the explicit PDF cases below; there
is no general failed-decode retry, prefix search or container rewrite.
Component/precision/sign/BPCC checks and centered-output metadata guards remain.
Missing canvas pixels are never synthesized.

If the original call rejects exactly where one terminal LF, CR or CRLF follows
EOC, these PDF-only entry points may decode the complete prefix once. Strict
APIs still reject the suffix. `discarded_pdf_eol_bytes` reports the one- or
two-byte PDF marker; additional whitespace, arbitrary tails, truncated prefixes
and earlier structural errors are not admitted. Valid containers ending in
similar payload bytes are not shortened. The original attempt retains its
input/resource checks, and allocation, limit and deadline errors are not retried.
Codestream byte/work counters describe the successful normalized input, not
the failed attempt or a new global work budget.

After an original `InvalidTilePart` rejection, a separate recovery admits
uniform, nonzero `TNsot` declarations that encode the final zero-based index
instead of the number of parts. Every observed tile must have its complete,
sequential `0..=TNsot` sequence, with the reported failing SOT at the final index,
validated `Psot` boundaries and an exact terminal EOC. Only count bytes change;
the corrected codestream is strictly parsed before ordinary PDF decoding.
No missing parts are inferred. `corrected_tile_part_count_fields`,
`tile_part_count_repair_copy_bytes` and `tile_part_count_repair_work_bound`
report the actual correction and its separately admitted copy/scratch/work
envelope. Strict decoding remains unchanged. Truncated, inconsistent,
out-of-order, zero/maximum-count and over-budget cases are not repaired.

`inspect_pdf_compatible(input, options)` returns owned full-SIZ coding metadata
under the same bounded container/EOC/count admission. It does not execute packets or
entropy, select a crop, discard a trailer or promise a decoded image.
Initial empty MQ contributions are rejected by default. The optional native-only
`pdf-mq-recovery` feature allows only a first, exactly one-pass, unterminated
legacy MQ contribution through the common PDF decode APIs; termination checks,
HT/mixed modes and later empty prefixes are not generalized. It executes real
MQ virtual FF fill and reports `empty_initial_mq_prefixes`, preserving the
pre-fill snapshot for later real-byte replay. Strict and individual recovery
APIs remain unchanged.

This scoped TLS policy is native/MSRV-tested, **not included in pinned Verus
qualification**; the unsupported combined verifier/profile build is rejected.
The supplied handcrafted control is not independently established conforming;
normative initial-contribution legality remains open in #293. Complete
fallibility and raw/JP2 feed/resume remain separate. A caller-selected
`cooperative-deadlines` scope covers repair and decode without resetting it.
These are final-input compatibility APIs, not `NeedMoreData` or streaming-pause detection.

### Explicit bounded terminal-trailer recovery

The four `*_recover_trailer_selected(input, options, selection)` APIs cover
raw/JP2 input and typed/centered reconstruction output. After all scheduled
packets and bodies complete, they may discard at most sixteen terminal bytes,
cumulatively across the selected tiles in this call. Only a final tile part
without packet-length tables or packed-header metadata anywhere in that tile is
eligible. The report gives the exact `discarded_tile_trailer_bytes`.

The completion scan resumes at the actual unclaimed suffix; packet headers,
bodies and entropy are never retried. No earlier input prefix is searched,
copied or trimmed. Genuine packet errors, strict container/profile checks,
selection geometry and centered-output restrictions remain unchanged. The
additional metadata scan obeys the existing work cap; existing decoder counters
remain stage-local, not a new global work/allocation budget.

This is explicit damaged-input policy, not normative JPEG 2000 padding or
permitted whole-packet truncation support. Strict APIs still reject trailers.
No shared mode or allowance state is installed. EOC, dimensions, missing tiles,
MQ compatibility, cooperative deadlines and feed/resume remain separate.

### Explicit sole-present-tile recovery

The `*_recover_present_tile_selected(input, options, selection)` APIs are
available for raw/JP2 input and typed/centered reconstruction output. For a
full-image request without a region, they may select one tile only when all
supplied tile parts belong to it and more tiles are advertised. Explicit tiles,
tile sets and regions retain normal selection behavior; an absent requested
tile still fails.

The result reports `selected_present_tile`, the full original SIZ canvas,
requested reduction and `full_canvas_sample_bytes`. The returned image keeps its
actual crop/origin/grid, never a padded or relabeled canvas. Inspection remains
metadata, not entropy success. New nonzero tile/origin placement controls and
native reduction tests qualify the implemented placement behavior.

Automatic recovery additionally checks a conservative full intended-canvas
sample bound at the requested reduction using eight bytes per final output
component, after JP2 mapping. This is not a peak/live-memory budget or permission
for an embedding to allocate arbitrary renderer buffers. Missing pixels are
never allocated by the recovery API. The centered path preserves fractions and
overshoot, using `decode_codestream_reconstructed_selected` rather than a
clipped typed image; NLT/palette/channel restrictions remain explicit.

Strict defaults are unchanged. This policy does not repair EOC, dimensions, MQ
damage or trailers, and does not add a deadline or general feed/resume state.

### Route a single-image JPX input

Select the route from the input's declared profile and the embedding's required
output, not by retrying a failed JP2 decode with relaxed admission:

| Required output | Explicit JPX API |
|---|---|
| One codestream's typed samples, with its associated palette/channel mapping | `decode_jpx_codestream(input, codestream_index, options)` |
| A region/native resolution of that codestream | `decode_jpx_codestream_selected(input, codestream_index, options, selection)` |
| Converted color, rather than typed component values | `decode_jpx_codestream_color` / `decode_jpx_codestream_color_selected` |
| A layer's registered channels and opacity | `inspect_jpx_layers`, then `render_jpx_layer(input, layer_index, options)` |
| An actual composition or animation frame | `render_jpx_composition` / `render_jpx_frame` |

```no_run
use jpeg2000_decoder::{DecodeError, DecodeOptions, TypedImage, decode_jpx_codestream};

fn decode_embedded_jpx(
    input: &[u8],
    codestream_index: usize, // Supplied by the embedding's selection policy.
) -> Result<TypedImage, DecodeError> {
    decode_jpx_codestream(input, codestream_index, &DecodeOptions::default())
}
```

A single opaque image does not require animation or composition. Conversely,
decoding a codestream is not equivalent to rendering a layer assembled from
multiple codestreams, applying layer opacity, or compositing layers. Do not
silently pick index zero for an ambiguous input. A static JPX without frame
instructions has no frame zero; use the explicitly selected layer instead.
Color and rendered output use 16-bit channels, not necessarily the component
precision returned by typed decoding.

The JP2 routes retain their JP2-compatibility and single-codestream requirements;
a JPX-only compatibility list is not admitted there. JPX inspection/decoding is
not a complete file-conformance or reader-requirements validator. An embedding
must establish the required feature/selection contract rather than treating a
brand or successful inspection as proof that arbitrary JPX semantics are
supported. The [single-image routing control](validation/VALIDATION.md#single-image-jpx-routing-control)
declares the narrower independently checked input and expectations.

## Select a region or native resolution

```no_run
use jpeg2000_decoder::{
    DecodeOptions, DecodeSelection, ImageRegion, decode_codestream_selected,
};

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let input = std::fs::read("image.j2k")?;
let selection = DecodeSelection::full_image()
    .with_region(ImageRegion::new(0, 0, 256, 256))
    .with_discard_levels(1);
let image = decode_codestream_selected(&input, &DecodeOptions::default(), &selection)?;
# let _ = image;
# Ok(())
# }
```

Regions use absolute, half-open SIZ image-reference-grid coordinates. Discarding
resolution levels selects native wavelet resolution, not a resize of a fully
decoded image. A selection must fit the input's actual origin and geometry.

## Keep reconstruction headroom

```no_run
use jpeg2000_decoder::{DecodeOptions, decode_codestream_reconstructed};

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let input = std::fs::read("image.j2k")?;
let options = DecodeOptions::default();
let reconstructed = decode_codestream_reconstructed(&input, &options)?;
for component in reconstructed.components() {
    // Centered value = sample / 2^fraction_bits, before rounding or clipping.
    println!("{:?}: {} fractional bits", component.info(), component.fraction_bits());
}
let typed = reconstructed.typed(options.limits())?;
# let _ = typed;
# Ok(())
# }
```

This strict, full raw-codestream API returns the existing
`image::DecodedImage` / `DecodedComponent`, not RGB or normalized planes.
Wavelet/component transforms and resource limits are shared with typed decoding.
For accepted inputs, `typed` reproduces `decode_codestream` under the same limits.
Every NLT declaration, including identity and tile-local declarations, returns
`UnsupportedFeature { feature: "nonlinear transforms on reconstruction samples" }`
after any parsing/reconstruction error. No failed decode is retried.

Samples retain signed centered `i64` headroom and per-component `fraction_bits`.
Image origins/extents and component dimensions, subsampling and raw CRG
registration are unchanged. Component coded-grid origins are the image origins
ceiling-divided by component subsampling; registration describes physical phase,
not extra decoded pixels. Consumers choose interpolation policy, widen operands
to `i128` before weighting, retain fractions, then round centered values once
(half away from zero), level-shift unsigned output and clamp to precision.

There is no reconstructed selection/container/recovery API in this increment.
Palette/channel mapping and color conversion are not applied or implied.
Reconstructed recovery output remains future work (#296/W19).
Recoverable allocation is still incomplete (#287); this API does not claim that
every allocation failure returns an error.

## Resource limits and errors

```no_run
use jpeg2000_decoder::{DecodeOptions, ResourceLimits, decode_codestream};

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let limits = ResourceLimits::default()
    .with_maximum_input_bytes(64 * 1024 * 1024)?
    .with_maximum_work_units(10_000_000)?;
let options = DecodeOptions::new(limits);
let input = std::fs::read("image.j2k")?;
let image = decode_codestream(&input, &options)?;
# let _ = image;
# Ok(())
# }
```

Limits cover input, output, dimensions, components, tiles, packets, metadata,
code-blocks, frames, and work. Callers can tighten the hardened defaults.
Inputs exceeding those bounds return typed `DecodeError` values; a valid
standard feature may still exceed the configured resource profile.

Errors distinguish malformed input, unsupported features or profiles, invalid
selections, resource exhaustion, and I/O. Applications should not treat a
successful metadata inspection as successful pixel decoding.

## Scope

- Decoder features from JPEG 2000 Parts 1, 2, 9, and 15.
- Legacy MQ/Tier-1 and high-throughput HTJ2K block decoding.
- Reversible integer and deterministic fixed-point irreversible transforms.
- JP2 palette and channel mapping; pinned sRGB, grayscale, and sYCC conversion.
- JPX explicit codestream/layer/frame selection and bounded composition.
- JPIP message parsing, transactional databin caching, and reconstruction;
  network transport and request scheduling are not provided.

Encoding, an ICC color-management engine, automatic handling of arbitrary
color-space registry additions, and internally parallel decoding are not
provided. See [supported profiles and limitations](SUPPORTED.md) for details.

## Proofs and testing

### Repository layout

- [src/](src/) is the single executable decoder used by Cargo and Verus.
- [decode.rs](src/decode.rs) defines shared decoder types and preserves the public
  API through re-exports. Its real Rust child modules separate responsibilities:

  | Responsibility | Implementation |
  |---|---|
  | Public codestream and container entry points | [api.rs](src/decode/api.rs) |
  | Component/resolution/subband geometry | [geometry.rs](src/decode/geometry.rs) |
  | Precinct and code-block planning | [planning.rs](src/decode/planning.rs) |
  | Coefficient preparation and reconstruction | [reconstruction.rs](src/decode/reconstruction.rs) |
  | Full/selected tile and layout execution | [execution.rs](src/decode/execution.rs) |
  | Palette, channel and selected-color output | [output.rs](src/decode/output.rs) |
  | Region, tile and resolution selection | [selection.rs](src/decode/selection.rs) |
  | Code-block/subband decoding and prepared-image API | [code_blocks.rs](src/decode/code_blocks.rs) |
  | Checked indexing and coordinate arithmetic | [arithmetic.rs](src/decode/arithmetic.rs) |

  Contracts and loop invariants remain attached to those executing bodies.
  [Proof support](src/decode/proof_support.rs) stays ghost-only; the private
  [tests](src/decode/tests.rs) retain their logical `decode::tests` identity.
- The other decoder components use the same parent/child organization:

  | Parent facade | Responsibility-based implementation |
  |---|---|
  | [codestream.rs](src/codestream.rs) | [Marker parsing, geometry and profile admission](src/codestream/) |
  | [packet.rs](src/packet.rs) | [Headers, tag trees, progression and retained bodies](src/packet/) |
  | [tier1.rs](src/tier1.rs) | [Legacy passes, HT streams, cleanup and refinement](src/tier1/) |
  | [image.rs](src/image.rs) | [Typed layouts, component transforms and image composition](src/image/) |
  | [transform.rs](src/transform.rs) | [Quantization, wavelets and arbitrary kernels](src/transform/) |
  | [color.rs](src/color.rs) | [Channel admission, conversion and crop](src/color/) |
  | [jp2.rs](src/jp2.rs), [jpx.rs](src/jpx.rs), [jpip.rs](src/jpip.rs) | [JP2 boxes](src/jp2/), [JPX layers and frames](src/jpx/), [JPIP messages and databins](src/jpip/) |
  | [refinement.rs](src/refinement.rs) | [Executable model-linked helpers](src/refinement/), not a second decoder |

  Shared types and existing public paths remain in their parent namespaces.
  Executing bodies are real Rust modules, not included source fragments.
  Private test files and ghost-only proof support are separate; ghost includes
  retain their original logical parent namespace. The mathematical model files
  are not split or substituted to meet a runtime-file size target.
- [specs/](specs/) and [proofs/](proofs/) contain maintained semantic models
  and proofs, not generated run results.
- [validation/](validation/) contains the reusable harness, regression tests,
  pinned oracle configuration, corpus manifest and JSON schemas.
  Its [technical reference inventory](validation/normative-coverage.json)
  links implementation, model, contract and test symbols; the accompanying
  [schema](validation/normative-coverage.schema.json) validates those links.
  These are required validation inputs, not a progress ledger or a
  standards-conformance certificate.
- Generated reports, native reference builds and fuzz artifacts belong under
  ignored `target/`, not in the repository root or versioned source.
  Personal execution plans, approval correspondence and session logs do not
  belong in the published tree.

- [Proof architecture and reproduction](PROOFS.md)
- [Decoder validation and external conformance inputs](validation/VALIDATION.md)
- [Contribution and local checks](CONTRIBUTING.md)
- [Standards and implementation references](REFERENCES.md)
- [Third-party notices](./THIRD_PARTY_NOTICES)

Rust builds and Verus verification share [src/](src/) as the executable source
of truth. [specs/](specs/) and [proofs/](proofs/) contain proof-only models and
lemmas. Verification is not a substitute for official test vectors, numerical
conformance, or independent review of the specifications.

The crate package contains runtime source, public documentation and the Rust
model/proof files referenced by its conditional modules. Keeping those files
available allows an unpacked source tree to be formatted and inspected without
inventing replacement specifications. Ghost-only modules remain disabled in
ordinary decoder builds; they add no default Cargo dependency.

Verification binaries, CI configuration, validation tools and oracle builds
are not bundled. Reproducing the complete verification and comparison workflow
still requires the exact repository revision recorded by `git.sha1` in the
package's `.cargo_vcs_info.json`, with the pinned tools described there.
Including proof source is not itself a successful verification result.

## Security

Follow [Microsoft's security reporting policy](SECURITY.md), not public issue
reports, for suspected vulnerabilities or sensitive reproductions.
The [threat model](THREAT_MODEL.md) describes the input and tooling boundaries.

## License

First-party source is licensed under the [MIT license](./LICENSE).
Derived HT VLC lookup tables retain the upstream BSD-2-Clause notices in
[THIRD_PARTY_NOTICES](./THIRD_PARTY_NOTICES).
