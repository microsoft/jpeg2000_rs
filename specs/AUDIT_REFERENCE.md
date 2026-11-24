# Detailed semantic audit reference

Start with the [human-auditor landing guide](README.md) for purpose, reference
status, component navigation and two contract-reading examples. This reference
preserves the former guide's detailed semantic explanations and local boundaries;
it is not a chronological completion ledger or a substitute for the current
contract boundaries in [PROOFS.md](../PROOFS.md).

`part1_parse_packed_fragment` binds raw marker/index bytes, full parser
state and every next-index/fragment-count/accumulated-byte frame, including
counter-before-error and header-byte-before-work-failure commits.
`part1_parse_ppm_frames` and its source-derived traversal retain the
fragments-zero bypass, all big-endian frame lengths/starts, checked error
offsets and post-push tile-part limit. Two exact contracts consume genuine
charge/read producers without normalized state, admitted frames/payloads,
extra trust/caps/pins/budgets or termination bypass. PLM/PLT, final metadata
and outer parser/F2/F4/F8 joins remain separate.

`part1_mct_graph*` composes actual full raw MCT parameters, first record
lookup, unique ID/kind arrays, real collection admission and native
stage/graph construction. Checked count arithmetic models intermediate
overflow before division/subtraction, not merely the final mathematical
shape. Four exact contracts bind all cloned array/collection/wavelet/stage
fields and every early error. Empty-order bypass, repeated raw order IDs,
first duplicate records, zero-index optional references and raw empty stages
are retained without normalized shape/registry or prepared-graph premises.
No trust/cap/pin/budget or termination bypass is added. Actual parsed-state
production and outer file/layer/F2/F4/F8 joins remain separate.

`part1_mct_registry_*` binds actual last-element-only array/record admission,
first-ID replace-or-append and exactly-one ID/kind borrowed lookup. Full
private views retain arbitrary array numeric fields and all record/collection
references. Earlier duplicates, ID-zero entries, other-kind matches, invalid
dimensions and numeric encodings are not normalized away. The root/traversal
equality covers early duplicate failure; unit-return mutations bind complete
old/final vectors without signature changes. Seven exact contracts leave
graph dimensions/resolution and outer joins separate, with no unique-registry
premise, supplied lookup result or trust/cap/pin/budget change.

`part1_consume_mct_fragment` composes the actual staging, first-ID lookup,
exact completion, swap removal and reconstructed source bytes with
`part1_parse_mct`. Full private observations bind arbitrary descriptor/
next/final/offset/data fields and completed IDs on every result. The actual
component limit derives the square-times-eight byte cap. Full-descriptor
continuation checks, append-before-error commits, initial-only completed
rejection, first-fragment error offsets and continuation duplicate-ID policy
are preserved. Four exact contracts add no normalized fragment, supplied
payload/array result, trust/cap/pin/budget change or termination opt-out.
Graph replacement/resolution and outer joins remain separate.

`part1_parse_mct` binds the actual full raw numeric array to source bytes and
limits. Header/alignment/component-square checks precede all actual values.
Signed16/32, packed64, IEEE32/64 and generic binary-to-Q32 producers compose
through the sole element body, not converted-value banks. Existing ATK
numerical denotations are reused with exact unit-error projection and the
original MCT exponent guard. Native zero/nonfinite/tie/underflow/overflow
semantics and source-derived read/count bounds require no normalized-value
premise, trust/cap/pin/budget change. Seven exact contracts leave actual MCT
fragment/graph and final outer joins explicitly separate.

The MCT value fold makes positive format strides and incomplete-element
rejection explicit. Remaining-byte termination is checked in the complete
root, not by a codestream-only check; no executable decoder change or
termination opt-out is used.

`part1_consume_mcc_fragment` composes the real staging, exact completion,
swap-remove, stored-offset reconstruction and actual MCC parser, binding both
pending and completed vectors on success and every failure. The actual scans
and `part1_prepare_mcc_fragment` derive all header/continuity/byte/next bounds
from raw bytes and arbitrary prior fields. Append-before-error and removal-
before-record-error commits remain explicit; continuation completed-ID policy
is not strengthened. Private full-state observations and actual vector/byte
producers add no normalized-state, reconstructed-result or graph-success
premise, trust/cap/pin/budget change. Remaining outer joins stay separate.

`part1_parse_mcc` and `part1_mcc_collection` bind the actual complete raw
record/collection Results, including all route, array/dependency and wavelet
fields. Header/limit and kind/list/descriptor/type/depth/signed-offset order
remain explicit; terminal admission precedes parallel conflict checks.
Actual routing, signed conversion, list equality and overlap producers
provide values and bounds, not successful graph or normalized collection
premises. Private views observe every physical field. The real parallel
check rejects cross-collection intersections without adding same-collection
or unrelated metadata policy. Five exact contracts introduce no trust/cap/
pin/budget changes. Numeric arrays, fragments/graph and final outer joins
remain separate.

`part1_parse_mco` and `part1_parse_mcc_component_list` bind actual raw routing
syntax, complete lists and every external-cursor error commit. MCO's empty
zero-stage order, count/duplicate/nonzero ordering and raw encounter order
remain explicit. MCC's width flag is independent of component count; header
advance, count/length admission and per-reference bounds/membership checks
retain exact cursor semantics. The sole actual membership scan is observed
by `part1_mcc_reference_present`, not supplied as an accepted-reference bank.
No route/graph-success premise, trust, cap, pin or budget change is added.
Actual numeric/collection/fragment/graph and outer file/F2/F4/final F8 joins
remain separate.

`part1_validate_progression_changes` binds the real read-only semantic
validator to raw records/styles/layers and actual work limits. Shape folds
observe real style lookup/depth/count arithmetic before budget and record
checks. Owner folds observe the sole native coordinate loops, binding all
partial bitmap effects for arbitrary inputs. No valid-window/style/bitmap
premise is consumed. Partial overlap is legal only when each record adds a
fresh active coordinate, and final full coverage is required. Empty bypass,
heterogeneous/invalid styles and calculated-work-before-record precedence
remain explicit; actual parser work counters stay untouched. Existing range/
contains models and the real completion scan compose without result banks,
new trust, caps, pins or solver-budget changes. Remaining outer joins remain
separate.

`part1_parse_poc` binds actual raw syntax to the complete progression-record
Result, using real byte/component reads and source-derived count/alignment
geometry. Threshold257, empty/alignment/order precedence, all physical raw
fields and the Csiz256 zero-end encoding remain explicit. Generic component
reads retain their nonunit-width two-byte fallback and distinct checked
segment-offset failures. `part1_poc_record` reuses the existing progression
order mapping without normalizing other fields or assuming valid ranges.
Three exact producer contracts add no trust/cap/pin/budget changes; actual
downstream range/coverage/duplicate validation and outer file/F2/F4/final F8
composition remain separate.

`part1_parse_atk` composes actual shared charge, full raw payload production
and first-index kernel replacement, framing all parser/eight extension fields.
`part1_atk_payload`, header/step/terminal folds and `part1_kernel_coefficient`
observe the sole real native bodies. They retain every raw descriptor/flag,
offset/exponent/residue/coefficient field and all sixteen physical coefficient
bytes. Arbitrary reader widths/types, integer sign extension, exact failure
offsets and first-error/terminal order are explicit without normalized kernels
or prepared step/byte/result banks. Equivalent bounded copying, safe casts
and standard fresh-query isolation add no trust, cap, pin or solver-budget
change. Remaining metadata/layout/file/F2/F4/final F8 joins remain separate.

`part1_parse_tlm` binds the actual raw header/record Result and all three
mutable frames: parser, external next-marker index and eight-field extension
owner. Real shared charge precedes index matching and increment, style,
alignment, tile bounds and minimum length. `part1_tlm_records` observes the
actual append/error prefix over arbitrary old records; absent tile indices,
zero tile counts and index255-to256 commits remain explicit. Actual style
primitives and standard remainder lemmas derive bounds from source, without
valid-row/budget premises, normalized owners, result banks, trust or pin/cap/
solver changes. Remaining metadata/layout/file/F2/F4/final F8 joins stay separate.

`part1_parse_nlt` composes real metadata/work charging, complete actual raw
payload production and first-component/default registry replacement.
`part1_nlt_payload` retains every raw and decoded nonlinear field through
header, gamma and LUT admission. Gamma's five words, domain/count/bit/width/
length/value ordering, 32-bit special case and retained raw parameter tail
remain explicit. `part1_copy_segment_tail` and `part1_maximum_u32_for_bits`
observe actual native loops with total functional contracts. Parser and all
eight extension fields, partial charge failures and later duplicate records
are framed without supplied parsed records, successful budget premises or
normalized registries. Existing safe precision/sign primitives and standard
array extensionality add no codec trust or pin/budget changes. Remaining
metadata/layout/file/F2/F4/final F8 joins remain separate.

`part1_parse_cap` and `part1_parse_profile_number` bind actual raw CAP and
PRF/CPF Results. `part1_set_bits_prefix` observes the real 32-bit count loop;
`part1_marker_words` and `part1_marker_word_sequence` observe the sole shared
word traversal, not an executable proof-only decoder. The real callers
derive its start bound; the shared helper also explicitly rejects arbitrary
out-of-range starts and has no precondition. Short-header/zero-mask/exact-popcount-length and
nonempty/even-length/last-word-zero ordering remain explicit. All raw mask
bits and word values are retained; actual getters do not impose admission.
No normalized profile, prepared parsed-result bank, new marker/value policy,
trust, budget or verifier-pin change is introduced. Remaining metadata/
layout/file/F2/F4/final F8 joins remain separate.

`part1_parse_cbd` composes the real shared charge and raw descriptor loop,
binding the complete parser and all eight extension fields on success and
failure. `part1_cbd_run` retains the exact valid prefix on invalid precision;
`part1_cbd_expand` retains repeated-zero-count behavior rather than imposing
a normalized owner. Count/length admission precedes the original depth
clear, while charge precedes header checks. Real byte/precision/sign
producers supply all bounds and values. No prepared depths, successful
admission premise, runtime cap/policy, trust or verifier-budget change is
added. Remaining metadata/layout/file/F2/F4/final F8 joins remain separate.

`part1_parse_dfs` and `part1_parse_ads` compose real charge, sole actual
payload producers and first-match registry updates, binding complete parser/
all-eight-field extension states on both success and failure.
`part1_dfs_payload`, `part1_ads_payload` and `part1_unpack_two_bit_values`
consume only raw source bytes/cursor/count/terminal inputs. Descriptor/index/
length/value/padding order, DFS-unused-slot permissiveness, ADS-zero counts
and first-duplicate replacement remain explicit. Every bounds/frame fact is
derived internally; no decoded-vector or normalized-registry premise, trust,
cap or verifier-budget change is introduced. The safe mask and shared bit
primitive are proved equivalent to original operations, not lookup-result
banks. Remaining metadata/layout/file/F2/F4/final F8 joins stay separate.

`part1_parse_rgn` binds raw ROI bytes/count/offset to the complete native
index/shift Result without a new shift or marker policy. `part1_parse_crg`
composes the actual metadata/work charge and source-derived registration
prefixes, binding the complete parser and all eight extension fields on
every error and success. Charge-before-length/duplicate ordering and exact
partial counter commits remain explicit, including empty markers and raw
unrelated owners. `part1_segment_byte` retains distinct cursor/segment
error offsets; `part1_metadata_byte_limit` is the actual field observation,
not a supplied budget. No normalized owner, prepared registration/result
bank, trust, cap or pin change is added. Remaining metadata/layout/file/
F2/F4/final F8 joins stay separate.

`part1_parse_qcd_payload` and `part1_parse_qcc` bind actual raw quantization
bytes to every native style/guard/count/step field, all 97 physical slots
and exact malformed offsets. Actual raw style counting, component-index
decoding and word reads supply all intermediate values, not admitted
counts or prepared results. Empty/style/length/unscaled-lowbits/capacity/
checked-step order and QCC component precedence are retained. Derived and
indexed modes, raw guard bits, depth/direction truncation and unused zeros
are explicit. No marker/scalar-compatibility/cap validation is newly added;
QCD-before-COD remains supported. Opaque mathematical folds observe real
loops rather than implementing a second decoder. Remaining metadata/layout/
file/F2/F4/final F8 joins stay separate.

`part1_parse_component_index` and `part1_parse_coc` bind actual raw component
index/COC Results and every CodingStyle field, including untouched direction
and precinct defaults. The sole actual `prepare_coc_payload` body proves its
43-byte scratch prefix/length from source bytes and raw defaults; the real
COD body then supplies the complete style before selector replacement.
Threshold257, truncation/component/SCOC/DSC/capacity/COD error order and
default progression/layers/MCT/SOP/EPH/depth inheritance remain explicit.
No marker/registry/default validation, normalized style, prepared payload,
result bank, trust or solver/resource-budget change is introduced. The
preparation/composition split isolates queries rather than duplicating an
executable parser. Actual main/tile callers use these bodies; quantization,
remaining metadata/layout/file/F2/F4/final F8 joins are separate.

`part1_parse_cod_payload` binds actual raw COD bytes to every native style
field and default/precinct slot, not an admitted style or lookup result.
Ordered flags/progression/layers/MCT/depth/block/length admission and the
lazy explicit-precinct capacity check retain original first errors.
Arbitrary transform indices remain raw metadata. Actual main/tile/COC parser
callers use the sole bodies and shared proved Tier1 block-style primitive.
No normalization, validity/budget premise, trust or production cap change is
added. Remaining metadata/layout/file/F2/F4/final F8 stay separate.

`part1_parse_siz` binds actual raw SIZ bytes to every native ImageSize field,
all private component slots and raw r_siz, not supplied parsed geometry.
Header/first-tile/length/geometry/component/descriptor/array/resource order,
paired sticky uniform flags and unused defaults remain explicit. No marker
identity validation, normalized metadata or admitted-image premise is added.
The actual parser checks SIZ before invoking this sole body. The real reader
already binds its segment bytes; remaining metadata/tile/layout parsing and
file/F2/F4/final F8 joins remain separate.

`part1_codestream_*` reader models consume actual raw input/limits and all
cursor/work/packet-counter fields, not supplied parsed results. They retain
marker validation, source-derived segment payload, standalone advancement,
EOC search and partial error/resource commits in native order. Constructor
and operation observations bind every field without normalized cursors or
valid-input/budget premises. Actual header/tile parsers consume these bodies;
marker-specific metadata, full layout parsing and outer file/F2/F4/final F8
remain separate.

`part2_decode_typed_layout` and `part2_typed_layout` bind actual complete
full/selected parsed-layout to final typed-image execution and every output
field. Real layout/byte decoding, typed conversion, source region production,
nonlinear owner mutation and final shape admission compose in source order.
The public raw byte entry points still parse first; no decoded/typed/region/
sample bank or normalized-success premise is supplied. Root denotations are
opaque outside explicit producer reveals, not trusted. The actual raw parser
functional Result and file/F2/F4/final F8 remain separate.

`part2_apply_nonlinear_regions` and `part2_nlt_component_mutation` bind
actual complete owner state AND Result, including failed-component rollback
by original deferred commit and already committed image prefixes. Raw source/
region/limit data derive every scratch slot, target and counter. Region,
duplicate/read/scalar/work, byte/coverage/conversion and metadata commit
order remain explicit under opaque terminating folds. No normalized inputs,
source coverage, scratch/sample/result banks or caller premises are supplied.
Whole typed/parser/file/F2/F4/final F8 composition remains separate.

`part2_nlt_inverse_sample` is the complete actual nonlinear sample producer
from raw source/component/transform, including parameter decoding and all
gamma/LUT/complement/unknown-kind/target-range behavior. Parameter and curve
models are derived real producer stages, not supplied results. Top-level
gamma/dispatch bodies are opaque outside the actual producer's explicit
reveals to bound context, not trusted. Fractional
denominator, ordered source/target scale admission, checked overflow and
rounding remain explicit. No descriptor normalization, caller premise,
trusted adapter or analytic accuracy claim is added. Whole region/typed/
parser/file/F2/F4/final F8 remain separate.

`part2_nlt_fixed_ln_q32`, `part2_nlt_fixed_exp_q32` and
`part2_nlt_fixed_pow_reciprocal_q32` compose actual raw normalization and
bounded series execution. Opaque high/low and 20/24-term suffixes retain
every checked failure, original normalization tickets, signed division,
Q32 rounding and final range/shift order. Native frames and termination are
proved without a positive-log premise or supplied series/results. These are
exact computational denotations, not real analytic accuracy/conformance
claims. Actual gamma/dispatch/region/typed/parser/file/F2/F4/final F8 joins
remain separate.

`part2_nlt_lut_sample` binds actual raw LUT inverse execution, not supplied
lookup results. Its helpers retain ordered admission, checked source/position
arithmetic, clamping, endpoint/point-read policy, native-width Rust division/
remainder and all interpolation/sign/type4 stages. Interpolation arithmetic
is opaque outside its own proved native body to bound context, not trusted.
No monotonicity, target-range or valid-input premise is added. Whole gamma/
log/exp/dispatch, region/typed/parser/file/F2/F4/final F8 remain separate.

`part2_nlt_round_ratio`, `part2_nlt_fixed_mul_q32`,
`part2_nlt_fixed_div_q32` and `part2_nlt_power_of_two` bind the actual
nonlinear scalar arithmetic, including intermediate overflow, distinct
denominator errors, half-away ratio rounding, signed truncation and the
original exponent ceiling. Shared checked-i128 and standard Rust-division
models retain exact operation order, not idealized unbounded final results.
Raw NLT getter posts do not validate descriptors. Whole nonlinear scalar/
region/typed/parser/file/F2/F4/final F8 composition remains separate.

`part2_collect_nonlinear_regions` derives the complete real typed-layout
region vector from source-owned transforms, not supplied region results.
First-specific/first-default selection, last tile-part override (including
empty), registered checked extents, component/tile order, lazy geometry,
clipping and raw transform fields remain explicit. Internal fold frames and
all bounds are proved without valid-image premises. Actual nonlinear sample
execution and whole typed/parser/file/F2/F4/final F8 remain separate.

`part1_validate_typed_output_shape` binds the actual final codestream output
validator, not only its scalar predicates. It checks raw input/layout/image
counts and extents first, then every signed or unsigned plane in source order,
without multiplying dimensions. Origins, descriptors, definitions and sample
values are intentionally not validated here. All loop/read bounds derive
internally, without a valid-image premise. Typed nonlinear finalization, raw
byte parsing and file/F2/F4/final F8 remain separate.

`part2_validate_execution_layout` composes the actual ordered component/tile
admission from raw parsed headers and logical counts. Component style lookup
errors, missing metadata, nonempty CBD mismatch and empty CBD bypass retain
native order; executable observation remains its actual no-op. Header views
contain observed native fields, not supplied validator/decoder outcomes.
Actual packet planning/component/file/frame composition remains separate.

`part2_validate_execution_style` observes only actual decomposition identity
and transform selection, with real DSC/ADS presence and ATK lookup. It does
not silently validate unused raw style fields. `part2_component_depths_equal`
is exact ordered precision/sign equality, not a valid-precision premise.
Actual registry-presence and getter observations are proved support. Whole
layout/decoder results and F2/F4/F8 file/frame joins remain separate.

`part2_copy_registered_opacity` describes the actual first-color, checked-area,
minimum rectangle, zero-padding and final-only target update. Pixel/row models
retain observed partial scratch state and address/read/store error order;
the owner remains unchanged on every copy failure. All inputs are raw, source
alpha is not substituted for its first color, and no prepared mask/read result
is assumed. Parsed-file dispatch and F2/F4/F8 composition remain separate.

`part2_apply_chroma_key_policy` distinguishes actual permissive general-layer
nonmatches from strict opacity's missing-sample error, without normalizing
planes or assuming coverage. `part2_set_layer_alpha_mode` preserves all raw
metadata/colors/samples and changes only the existing alpha representation,
or returns the caller's missing-structure offset unchanged. Actual source
coverage and prefix proofs establish the strict path. External-alpha copying,
file preparation and complete F2/F4/F8 remain separate.

`part2_normalized_component_chroma_keys` separates actual ordered descriptor/
checked-byte-count validation from payload admission and real key assembly.
`part2_append_component_key` preserves all original keys and offset until its
actual slice/normalization/first-key checks succeed. Both folds derive actual
data, not supplied outcomes; error inductions remain in proof support. This
closes per-component raw preparation only, not opacity or F2/F4/F8.

`part2_normalized_chroma_keys` names the actual raw metadata/precision/length
admission and full key output. `part2_chroma_key_bytes` gives the big-endian
value, while `part2_chroma_key_normalize` states masking, signed bias and exact
rounded normalized units. The actual code shares the proved unsigned-color
scalar; its failures are excluded by derived native admission/masking facts,
not a caller-supplied validity premise. Loop-only byte bounds remain in proof
support. Per-component descriptor preparation and opacity are separate work.

`part2_register_layer` derives the actual geometry and zero initialization,
then composes ordered row/column sampling through the actual pixel semantics.
The complete source owner/descriptor/grids determine every error, output plane
and final alpha flag. The row model preserves observable partial buffers on
late failure; its internal context contains raw inputs and actual derived
width, not a supplied success or decoder result. Standard-library seed/clone
facts establish initialization without a new trust adapter. Opacity, raw-key
normalization and complete F2/F4/F8 remain separate work.

`part2_registered_pixel` composes actual checked row-major addresses,
ordered color stores and final alpha read/store from the raw owner and
destination buffers. Its complete error result retains earlier color updates.
Missing alpha supplies the native opaque value; malformed alpha is not
normalized. The color-prefix denotation describes observable partial states,
while its inductions remain in proof support. Outer registration traversal
and full F2/F4/F8 composition are not implied by this pixel boundary.

`part2_native_registered_extent` names the raw native product, offset, rounding
headroom and typed result policy. `part2_registered_layer_geometry` composes
the real ratio/grid admission, ordered width/height and checked area. The
actual registration routine executes this same preparation body; successful
extent/shape values are not supplied as assumptions. Registered sample
traversal and complete opacity/normalization remain separate F2 obligations.

The F2 `part2_apply_chroma_key` model describes the actual general-layer
producer over the complete raw owner, not a supplied normalized image:
exact key cardinality, checked native area, per-channel equality and final-only
straight-alpha replacement. Missing samples are nonmatches; empty channel sets
match vacuously. The distinct strict opacity path is not claimed here.
Loop-prefix quantifiers and their inductions remain in proof support rather
than the auditor-facing semantics. Registration, raw-key normalization and
opacity composition remain open F2 work.

The native MCT owner views preserve every raw array field and all wavelet,
collection and stage fields, including complete ordered input/output lists,
None versus Some arrays/wavelets and ordered stage/collection sequences.
Their actual getters expose these complete values without geometry, precision,
matrix-shape or success premises. These are semantic inputs for the pending
actual collection/dependency/wavelet composition, not proof that those
algorithms or general MCT are already complete.

`part2_mct_dependency_row` now describes the complete actual reversible and
irreversible dependency row, including source/offset admission before matrix
lookup, the different triangular layouts, real prior-output prefix, positive
reversible scale and signed floor correction, and checked Q32 rescaling.
None, row-zero and unvisited malformed coefficients retain their native bypass
behavior; out-of-range precision is not normalized. The actual loops refine
the shared dot-prefix denotation, not a supplied row outcome. Full mutable
collection/stage traversal and general MCT remain separate work.

The deep native mutable-component view includes each actual reference,
geometry/subsampling field, dereferenced precision and every sample, not opaque
borrow identity. `part2_mct_find_component` denotes the real first matching
component, using the pinned standard-library first-index semantics. The actual
lookup proves complete duplicate/missing/error behavior over this full view;
malformed geometry and precision are not silently admitted as validity facts
for later collections.

The actual decorrelation sample store now refines the full deep component
update: exactly one in-range sample changes and every metadata/precision field
is retained; an invalid index retains all values and returns the real typed
error. Its caller preserves original output-read-before-destination-store
evaluation order. This is a real shared mutation boundary for pending mutable
collection proofs, not an assumed write or a normalized component premise.
The actual array store additionally frames every unselected component and
all metadata/precision/sample values on a destination or sample-index error.

`part2_mct_validate_layout` describes the actual readonly decorrelation
admission phase, including empty/invalid first sources, every source then
destination geometry/subsampling/sample-count/precision check, and reversible
source-zero precision. Matching zero dimensions/subsampling are not silently
rejected or treated as valid planes. The sole native phase was moved without
new allocation or execution-order changes and is called by the real collection.
This establishes its actual result from full raw component/index values,
not a supplied validation outcome.

The actual decorrelation work/scratch admission refines a complete result
and work-counter model. Checked product/total overflow precedes charging;
counter overflow retains the old value, while work-limit and subsequent
scratch arithmetic/byte-limit errors retain the actual charged value. Original
usize scratch arithmetic and evaluation order remain. Independent wide
references and exact limit-minus-one/limit/limit-plus-one cases check these
real thresholds; no adequate-budget assumption replaces admission.

The actual decorrelation preparation producer now constructs its real source
and destination indexes, validates raw layout, performs real ordered work/
scratch admission, and gathers the actual source precision vector. Its full
result and final work counter refine `part2_mct_prepare_decorrelation` over
the complete original component and collection values. Ordered lookup derives
the indexes from real component identities; no index list, valid layout,
successful preparation or admitted budget is supplied as a premise. Native
allocation and source-before-destination lookup order are preserved.
`part2_mct_decorrelation_pixel` now describes the actual complete source
snapshot, row computation and ordered destination stores, including both
scratch vectors and all partial error states. It does not receive precomputed
samples or supplied row results. `part2_mct_decorrelation` composes the actual
preparation, every real pixel and final-only precision updates into one
complete Result/components/work relation for the original native producer.
Duplicate component references, malformed raw descriptors, zero-sample paths,
first-error order and earlier state effects remain distinct. `part2_mct_dependency` now also closes the original actual dependency collection:
real checked coefficient dimensions, interleaved identity resolution, both-side
integer/layout validation, precise charged work and saturated scratch checks
precede actual cached-precision/pixel/final-tag composition. The source/store
loops are genuine shared production bodies, while dependency's previous-row
recursion and explicit source count remain distinct from decorrelation.
Wavelet intervals, interleaved source scaling, reverse actual 5/3/9/7 synthesis,
cardinality checks and complete pixel/collection state now also compose.
`part2_mct_transform` describes actual forward collection/reverse stage order,
including every previous update/work counter on an error.

The real owned-image and prepared-tile bridges derive their mutable inputs
from actual owner buffers and size metadata. Checked final-field borrow
promises reconnect actual transformed samples/tags to the original owners;
no successful decoder or transformation result is supplied as an input.
Prepared standard RCT/ICT similarly refines its actual full enabled/disabled
Result and shares the existing scalar implementation. Complete actual planned
coefficient/style/kernel preparation, optional MCT/standard transforms and
full/selected prepared assembly now compose without supplied decoder results.
Coherent current-main/hosted qualification and external conformance remain.

The four original single/multi-code-block and JPIP inner/transaction guarantees
are now complete native Result/full-state refinements. Follow
`part1_single_code_block_packet`, `part1_multi_code_block_packet`,
`part1_jpip_precinct_packet_inner` and `part1_jpip_precinct_packet` to the sole
actual header/reader/body/clone producers. The explicit local/truncation error
policy preserves original caller offsets without changing child decoder
errors; zero-policy legacy models remain exact specializations. Complete
bundle fields and real transaction rollback are modeled, not supplied outcomes.

## Frozen remaining public packet/JPIP boundary profile

This branch starts at unchanged `b5b0685`. The remaining native entry bodies are
`decode_single_code_block_packet`, `decode_multi_code_block_packet`,
`decode_jpip_precinct_packet_inner` and its actual
`decode_jpip_precinct_packet` transaction. These complete the original F5L/F5H
packet boundaries above the already-proved sole reader/tree/header, mixed body
and progression producers, not an image/parser theorem or normative endorsement.

Single-block admission uses the validated whole-payload reader (not prefix
admission), exact absent-packet trailing-data rejection, real header/tree state
and actual transactional mixed body decoding. It does not roll back prior
header/tree commits on a later body error. Multi-block admission retains raw
shared trees, physical arrays, all contexts, native marker differences, whole
body preflight and every earlier block's effects; its local arithmetic/header
errors use the caller offset, unlike the precinct helpers' zero-offset policy.
SOP presence there does not validate its sequence number.

JPIP writes all actual context layers and constructs its real inline packet
input. Its outer transaction clones/restores only states, contexts and subbands;
complete decoder preservation must follow from the real skipped-body path,
not a supplied clone/decoder result or an assumed rollback. All raw metadata,
malformed vectors/trees/retained decoder states, flags, caps and first-error
effects are admitted without normalization, success, budget or trace premises.
Faithful native subband cloning must preserve every scalar and both complete
raw tag trees. Unobserved readonly template metadata is not decoder output.

The four named actual entry bodies now refine `packet_boundaries.rs` without
input premises. The complete single and multi posts observe actual results,
every packet state/shared tree and entire decoder state/vector. Multi's real
header loop carries all partial reader/tree/state/count/storage effects.
Precinct and multi body paths now share the same executable preflight and
execution loops with an explicit pair of truncation/local error offsets;
decoder-origin errors are never remapped. Existing zero-offset relations remain
proved specializations, not widened assumptions.

The JPIP inner relation derives actual inline bytes, real context layers and
the native absent packed-header source, using the tiny actual constructor
observation from `85697b6`. Only relevant raw readonly fields are projected
into the shared precinct admission relation; no foreign clone outcome is
provided. Actual faithful subband `Clone` follows original field/allocation
order and preserves unused raw tree words. The original outer Vec clones and
restore statements prove full rollback through actual skipped-decoder and
identity frames, while retaining complete inner Result/state semantics.
This closes these named packet/JPIP entry guarantees, not an entire image/parser
theorem, normative endorsement or an automatic whole-epic/project claim.

Start the complete actual multi-tile-part chain at
`part1_progression_tile_decode`, then follow actual native grid/iterator
construction, raw packed/length input, boundary scan, context-layer writes,
real precinct/header/mixed coefficients, ordered accounting and finish.
`part1_packet_iterator_initial` and `part1_packet_context_layers` expose the
complete actual constructor/update values without changing execution.
The finite registry binds42 exact shapes, with40 real internal-consumer
contracts and honest standalone public API support. No trace/list/outcome
bank, normalized POC/grid/cursor or successful-budget premise is introduced.

## Frozen remaining actual progression profile

The next actual producers are `PacketGrid` construction/indexing,
`PacketIterator` construction/candidate decoding/iteration,
`ProgressionPacketIterator` construction/window/duplicate iteration, and
`decode_progression_tile_packets_selected`. Their contracts admit every raw
stored grid count/vector/offset, iterator cursor and nested default iterator;
stored candidate/packet totals are not assumed consistent with physical arrays.
Candidate advancement precedes decoding failures. Emission advancement precedes
late stored-total rejection. POC window advancement and duplicate suppression,
actual packed-byte reassembly and packet-length iteration, context-layer writes,
complete precinct-vector effects and late offsets/aggregates retain native order.
All first errors and partial state are observed without validity, normalization,
success, adequate-budget or supplied outcome/coordinate traces.

F5H owns only actual packet/grid/iterator/orchestration implementations and their
specifications/proofs. F5L owns the sole actual raw packed-header and packet-length
producer chain; Parent owns POC observations and typed limit getter facts.
Frozen `0da8f58` remains unchanged while this separate progression branch
continues. Completing a raw lookup/iterator stage alone is not full progression
or F5H completion.

The complete named actual grid/iterator and multi-tile-part caller join is now
in `packet_progression.rs` and `packet_tile.rs`. Native raw constructors,
lookups and both complete iterators feed the actual selected/public tile
packet caller. Its preparation derives packed bytes and expected lengths
through the sole real owner producers, not supplied results. Every progress
field, nested default/length cursor, context-layer write, seen value, statistic,
restart and late error is retained. Its complete post observes the real
`TilePacketDecode`/error and entire final precinct vector, without shape,
normalization, successful-decode, budget or coordinate/header trace premises.
This named producer closure does not assert the separate remaining public
single/multi-code-block/JPIP wrappers or complete F5H/normative/project scope.

Actual POC records are exposed as their complete ordered native values,
including duplicate/inverted/empty windows and progression-order tags.
Actual membership preserves its layer-end, resolution and component
comparisons without normalized-window premises. The existing typed
tile-part/component/resolution/layer cap getters expose only their real
fields; defaults, limits, API and execution are unchanged. These owner
facts feed the pending real progression iterator and packet caller, not a
supplied coordinate or outcome bank.
The complete actual native header/reader/raw-tree and single-precinct chain is
now bound by39 finite qualified whole-result/input recipes. Start at
`part1_packet_header_decode`, then `part1_precinct_headers` and
`part1_precinct_packet`: raw native metadata and actual bytes flow through
real style selection, SOP/prefix parsing, every mutable header association,
alignment/EPH, whole preflight, actual mixed coefficient execution and final
packed/inline accounting. Only packet state is restored on a header error;
tree/reader and later coefficient/counter effects retain their exact native
order. There is no supplied outcome/trace, normalized descriptor/window or
adequate-budget premise. Full progression/reassembly remain separate.

The actual component-style owner returns its complete native style/error with
logical-count rejection before physical-array lookup, including contradictory
counts. The complete native Tier1 byte parser preserves every flag, the exact
HT/mixed rejection masks and all256 input bytes. Public static APIs and the
actual codestream caller share one executable parser body. Closed owner
observations expose actual SOP/EPH fields and packed-header source presence;
presence is not inferred from byte length or fragment count. These facts feed
the actual tile/precinct composition and pending progression join, not a supplied style
or header outcome.

## Frozen actual precinct/progression orchestration contract

The composition boundary is the actual `decode_precinct_packet` and its
remaining progression caller, not a supplied header/result bank. F5L owns the sole complete
packet reader, raw tag-tree and header producer interfaces; this work consumes
those actual contracts without editing their algorithms or duplicating views.
F5H owns precinct/progression associations, native local progress and full
state/error/coefficient effects.

The precinct profile admits arbitrary stored states, contexts, decoder and
subband vectors; malformed geometry, overlapping raw subband ranges and absent
storage are not normalized away. It preserves original shape/cap/style and
SOP/packed-header selection checks, ordered actual per-block header calls,
alignment/EPH effects, complete body preflight before any coefficient execution,
and then actual selected mixed body transactions. Skipped Tier-1 execution
still consumes/checks real body ranges while preserving decoder state. All
native offsets, segment/pass/contribution counters, first errors and the final
packet-length check are included. This caller is not globally transactional:
earlier header/tree/decoder changes may survive a later error.

The first executable substage is the existing precinct body preflight and
execution loops, moved rather than copied when needed for complete loop
contracts. Their descriptor vectors are the caller's real native arrays;
closing the entire precinct contract must additionally derive them through the
actual F5L header producer, never assume their correctness or supply an outcome.

This body-loop substage now has unconditional executable relations to
`packet_orchestration.rs`: `part1_packet_body_preflight` and
`part1_packet_body_execute`, with complete raw local progress and the entire
decoder-state sequence. Its descriptor-slice view delegates the sole
`code_block_contribution_option_view`. A scoped actual mutable decoder borrow
and explicit nested-vector frame preserve all untouched elements and exact
late-error coefficient/counter effects. Its properties retain raw finished
cursors, advanced-end truncation and all skipped-execution decoders/counters.

The progression profile must additionally preserve actual coordinate iteration,
tile-part/packed-header/packet-length cursors, duplicate suppression, context
layer writes, resolution selection, earlier packet effects and all late checked
aggregate/consumption errors. Actual external owner interfaces are prerequisites,
not assumed successful traces. The intermediate body and association stages
alone do not close this boundary; the precinct join below closes the
single-packet caller. See the [complete mixed packet-body boundary](../PROOFS.md#complete-actual-mixed-packet-body-acceptance)
for the additional actual producers. A complete raw-input-to-frame theorem
is a separate claim, not implied by either local relation.

The actual precinct header association stages now refine
`part1_precinct_header_slot`, `part1_precinct_header_members` and
`part1_precinct_headers`. They invoke the actual `part1_packet_header_decode`
on each actual selected packet state/context/tree pair and carry every result
into the real descriptor slot. Raw overlapping subband ranges are retained:
the contribution count need not equal the number of final occupied slots.
Readonly admission precedes the scoped mutable header borrow; complete vector
length, untouched-element and selected-subband metadata frames are explicit.
Native force-bit omission in style equality is part of the actual policy,
not replaced by whole-struct equality.

### Complete actual TilePartPayload precinct composition

The original `decode_precinct_packet` now has an unconditional complete
Result/full-precinct relation to `part1_precinct_packet`. Its semantic input is
the actual `TilePartPayload`, not a bank of style, header or decoder outcomes.
Actual owner contracts derive component-style count/physical-array errors,
all byte-parser results, SOP/EPH fields and packed source presence. The real
shape, code-block/work caps and data-offset checks retain their original order.

Three actual production phases isolate marker/reader admission, native header
association, and alignment/EPH/body/accounting. Their code is moved, never
duplicated; descriptor allocation still occurs once, after the packet-present
bit. Prefix relations include the complete returned reader and original
borrowed byte slice. All helper contracts admit arbitrary raw metadata, state,
descriptors and cap values without success or budget premises.

The full join derives descriptors through the sole F5L header producer, then
preflights every body range before actual mixed legacy/HT execution. Packed and
inline paths preserve distinct physical cursors but common logical length;
SOP/EPH overhead, skipped execution and all final conversions are included.
Header/tree commits survive later EPH/preflight failures; decoder commits also
survive a later packet-length mismatch. Independent literal MQ and HT streams,
including nonzero HT coefficients, exercise these effects without using the
model or subject decoder as an expected-output oracle.

This closes this actual single-precinct packet boundary, not packet progression,
tile-part reassembly, packet-length iteration, JPIP outer transactions, general
codestream correctness or the F5H epic.

## Raw packed-header and packet-length inputs

[packet_input.rs](packet_input.rs) is the denotation for the actual packed
reassembly and packet-length input producers. `Part1PackedHeaders` includes the
entire source (None or raw marker storage, marker word and logical start), length
and fragments. `Part1PacketLengths` includes the entire None/PLM/PLT source and
both metadata counters; `Part1PacketLengthIter` includes that source and both raw
cursor/end values. No topology, valid marker, canonical integer, normalized
metadata, successful outcome or sufficient-budget hypothesis is required.

The source owner supplies closed `packed_packet_headers_view`,
`packet_lengths_view` and `packet_length_iter_view`; only the Result<Vec<u8>>
projection `packed_header_reassembly_outcome` is open. Reassembly consumes the
existing typed header-byte cap. Its private whole-scan record includes every
output byte, both positions and the actual remaining-segment counter. All scan
and byte-group recursion decreases come from the native traversal/guards.

The actual native `next_length` model retains early PLT cursor commits on late
errors, preserves arbitrary cursors for None, and never substitutes the stored
packet count for the actual encoded source. The metadata getters do not assert
that those independent fields agree. Existing associated `none` APIs delegate
the actual free constructors `packed_packet_headers_none` and
`packet_lengths_none`, avoiding an invented static-method proof binding.

## Native packet reader and raw tag-tree ownership

The actual typed factories `packet_reader_new`, `packet_reader_prefix` and
`tag_tree_new` obtain their caps from the sole `ResourceLimits` owner getters.
Their complete contracts use those closed owner projections, not caller-supplied
outcomes or assumed numeric caps. Existing associated constructors delegate to
these production factories; checked and prefix reader admission remain distinct.

[header.rs](header.rs) observes all eight packet-reader fields and its actual
load/read/word/admission effects, including header-cap-before-truncation,
stuffing checks before advancement and consumed-bit-before-work-limit failure.
Validated construction rejects an oversized input; actual prefix construction
does not. Alignment retains stuffing history. No initialized-reader or adequate
budget condition is a premise of any actual read operation.

[tag_tree.rs](tag_tree.rs) observes every raw level and node. The real public
decode uses its actual guarded path builder, node loop and reverse traversal;
the path is not an input to its public theorem. Empty storage, mismatched level
rectangles, duplicate/overlapping offsets, 64/65-level boundaries and arbitrary
low/value order remain native cases. Inherited-low stores precede a failing
read, and arithmetic address errors retain offset zero while path/node errors
use the actual reader cursor. Constructor limits and faithful raw cloning have
their own complete relations, without a validated-tree premise.

The packet-state projection preserves all five fields. The sole public Option
and Result contribution projections retain `None` versus `Some(empty)` and all
164 descriptor slots. These actual primitive producers are prerequisites for
the full header/probe/rollback relation below, not a supplied header or
successful decoder outcome.

The continuing actual header join is now complete as
`part1_packet_header_decode`: the production entry feeds real reader and raw
TagTree results into its real pass/Lblock/length grammar, Mixed probe and final
packet-state commit. Local next-state updates are not silently treated as public
commits. Public errors preserve packet state while retaining exact reader/tree
partial effects. Probe errors retain the already-read main cursor; only actual
legacy selection commits the probe. Every optional result contains complete
physical descriptor arrays, including unvisited storage.

The descriptor-fold bound comes from its actual 164-element arrays and first
failing check. It is not a normalized-count, sufficient-resource or supplied
trace condition on the native entry. Native header context/state fields remain
arbitrary; the model uses the real supported-bitplane/pass constants where the
actual producer checks them. Raw helper count165 and final conversion cases are
not erased. Precinct/progression callers must consume this actual producer
relation; their larger rollback and association claims do not follow merely
from this header result.

## Complete actual mixed native body and segment dispatch

`part1_code_block_body_staged` consumes the sole full native contribution view,
actual body sequence, raw decoder state and four real owner caps. It composes
the single `part1_code_block_body_prepare` producer and then the actual
`high_throughput` branch: `ht_packet_body_segments` or
`part1_legacy_code_block_body`. No route result is an input.
`part1_code_block_body_transaction` models the real whole-decoder clone/commit
operation. Both actual staged/public functions have unconditional complete
Result/state posts; their earlier selected posts remain available too.

`part1_tier1_segment` likewise joins the actual Tier-1 public segment dispatcher:
zero-pass rejection, then `ht_group_route` using the stored cleanup **option**,
then actual HT group or legacy segment execution. It does not replace the option
with a flag, normalize private state or introduce a decoder-validity premise.
The old conditional HT relation remains a proved consequence.

All native primitive/helper bodies and resource policies are preserved. In
particular, a zero-count empty legacy contribution can succeed while the HT
route rejects it; the legacy replay/input limit is not invented for HT decoding.
Selector-only loop invariants used for the former disjoint proofs are gone.
The actual shared header parser and complete precinct/packet caller remain
separate composition obligations, not assumed successful traces.

## Frozen actual HT packet contribution-body route

This stage is the actual HT branch of
`packet::decode_code_block_contribution_body_staged` and its outer transactional
clone/commit entry. The sole F5L contribution projection/getters supply every
native header field and both complete physical segment arrays; no competing
header view or parser is introduced. All native stored counts, malformed header
combinations, old decoder states and supplied body bytes remain admitted.

The sole actual common prefix refines `part1_code_block_body_prepare`; both
selected branches reuse that producer and its model. It checks exact body length and route, then sets zero
bitplanes before HT segment-count admission. HT traversal checks each actual
segment Result, pass count, native length/address arithmetic and exact borrowed
body subrange, then selects cleanup/placeholder/refinement using the current
decoder phase and cleanup flag. Decoder effects precede decoded-pass accounting;
offset/index updates follow. Final exact consumption and declared-pass mismatch
errors retain the staged partial state, while the outer real clone/commit
wrapper preserves the complete original decoder on every failure. The private
loop is unconditional; only the staged/public postconditions select the actual
HT header flag. Their profiles are not restricted to a normalized header or a
decoder whose coding style already guarantees successful HT execution.

The complete models are `ht_packet_segment_route`, `ht_packet_segment_body`,
`ht_packet_body_run`, `ht_packet_body_segments`, `ht_packet_body_staged` and
`ht_packet_body`. `HtPacketBodyProgress` represents every local progress field;
the native private record has one closed owner view. These relations include
the current cleanup flag, exact `None`/stored cleanup distinctions, original
decoder vectors/counters and all actual typed failure effects through the
existing Tier-1 producers. The optional public byte-slice view is open because
it contains no private fields; no private decoder representation is opened.

No supplied decoder/legacy outcome, header/shape normalization, success, trace
or adequate-budget premise is used. Empty slices route differently according to
actual state; `None` and retained empty data are not conflated. Legacy branch and
shared header parser are untouched. Shared contribution/zero-bitplane/route facts
are owned by F5L and consumed from their real implementations. Full header
parsing, mixed legacy/HT union and precinct orchestration remain separate
producer obligations; this selected body boundary is not full F5H completion.

## Frozen whole-decoder clone and actual selected HT group profile

The next boundary is the actual staged HT branch of `decode_segment`, selected
by HighThroughput coding or Mixed coding with a retained cleanup-plane option.
The selector is not normalized to the current-cleanup flag. Its whole-decoder
raw clone preserves every field, vector, malformed shape and retained state
through the existing sole F5L logical bitplane/MQ/legacy projections and three
actual data clone contracts. Original field/vector allocation order is retained.

The real packet-pass grouping, repeated skip-one/skip-two placeholder loop,
substantive byte entry and final clone/commit are modeled directly. Any failure
after staging preserves the entire original decoder, even if the staged copy
has partial counter/reset effects. Success commits the entire actual staged
state and reports the original packet pass count. No supplied clone/replay/
legacy outcome, normalized old state, valid stream/shape or sufficient budget
premise is introduced. The legacy dispatcher else remains untouched and outside
this selected-branch theorem until actual legacy composition is available.

## Frozen retained-refinement and placeholder orchestration profile

The next native boundary is the complete actual
`decode_high_throughput_refinement`, including arbitrary retained byte buffers,
cleanup planes, pass counters and flags. Its actual admission does **not** check
the configured pass limit or `maximum_passes`; those checks must not be invented.
The cumulative-byte check precedes cloning/appending the retained buffer, and
the 2046-byte check remains after those real operations. Nonempty input is
replayed from the retained cleanup plane through the actual complete refinement
producer, not from a supplied trace or the current output plane.

An empty concatenated buffer records refinement passes and segment accounting
without replaying or replacing the output plane. Empty input with nonempty
retained bytes instead replays those bytes. Replay rejection preserves the
entire decoder; successful replay stores plane/data/passes before checked
pass/segment accounting, so late errors retain prior writes. No normalized old
state, valid stream/plane, success or adequate-budget premise is admitted.

The accompanying complete `skip_high_throughput_segment` profile retains actual
phase/pass/set admission, placeholder/replacement flags and first-error writes.
A phase-zero placeholder clears retained refinement bytes/passes and the
current-cleanup flag, but preserves the old cleanup-plane option and output.
Set-count updates precede those resets; pass/segment updates follow. Byte/work
limits absent from this operation are not added. Staged multiple-group/mixed
dispatch remains a separate boundary requiring actual clone/legacy relations.

The existing two-statement retained-buffer reset is now shared by the real
symbol caller and phase-zero skip operation. Its unconditional whole-decoder
state contract isolates that frame join without changing operation order,
capacity, proof budgets or solver context flags. The void helper is referenced
as a proved implementation fact, not mislabeled as a named-Result contract.
Independent integration regressions also execute the existing real staged
packet-group loop, rollback and successive continuation/replacement calls.
Those regressions are not a substitute for a full clone/dispatch theorem.
The pinned non-Copy derived `Clone` implementations expose no functional
specification; full group closure must use actual raw cloning relations,
including the shared logical bitplane-state view, rather than opaque native
identity or a supplied legacy outcome.

## Actual legacy MQ/bypass three-pass boundary

[mq.rs](mq.rs) supplies a complete declarative MQ state/Result denotation.
The stored nineteen contexts are pairs of probability-state index and MPS bit.
The forty-seven probability transitions are an independent ghost sequence joined
to the production table, not an assumed transition trace. Initialization,
context mutation/save/restore, byte loading, conditional exchanges,
renormalization, exact work admission, consumed-byte reporting and the existing
predictable-termination test retain all native error priorities and mutations.
In particular, byte advancement can survive addition failure; code/count loading
can survive padding-counter overflow; a work-limit error retains its increment.

[legacy.rs](legacy.rs) composes those real MQ effects and the complete raw-reader
effects with actual significance, refinement and cleanup operations. The whole
bitplane state observes geometry, bitplane, both bool vectors and all three
completion flags. The plane observes all six words, sign, significance,
refinement and optional legacy bitplane of every coefficient. Context selection
uses the real complete ordered-neighborhood producer, including causal
suppression. Stripe, column and row folds model the actual optimized traversal,
not a normalized or reordered coefficient list. Cleanup includes run-mode
eligibility/interruption, the two uniform run bits, sign reads, remaining rows
and optional segmentation-symbol reads.

Native invalid states are not erased by constructor invariants: the pass
preflight checks geometry/vector lengths and completion order, while actual
coefficient operations retain their own different bitplane bounds. For example,
marking accepts the magnitude owner's native 0..383 domain, whereas refinement
first rejects bitplanes at or above 292. Both behaviors remain in the models.
Symbol/visit/plane/statistic changes before a later failure are retained.
No public pass assumes valid bytes, successful decoding, normalized words,
valid headers, adequate budgets or a supplied trace.

Opaque model phase boundaries control proof unfolding only. The concrete
production stages prove each phase against its body; both private reader-adapter
implementations delegate to proved actual readers. There is no second executable
decoder or uninterpreted successful entropy outcome.

The same module now composes actual segment scheduling and contribution replay.
`part1_legacy_segment` checks the real pass/byte/empty-segment admission before
reader construction, restores or initializes real contexts, runs the actual
MQ/raw pass loop, checks existing termination policy and commits accounting in
its real order. `part1_legacy_contribution` preserves exact replay-work charging,
retained-record take/append/restore, the real segment's result and final record
retention. Its starting numerical state and input bytes come from the actual
retained record, never from a supplied successful decoder outcome.

Complete logical bitplane and nineteen-context projections appear in both
whole-decoder and retained-record frames. The actual faithful raw plane,
bitplane and legacy-record Clone implementations preserve malformed shapes and
all words/flags and retain original field/allocation order. Private arithmetic
lemmas receive their six-word facts from those real native representations, not
from a normalized-coefficient premise. Native record restoration and data
append are verified operations, not assumed state transformers.

The actual route/pass/accounting getters and zero-bitplane setter supply native
owner facts for the next packet caller. The setter checks a previously stored
value before its phase/counter checks and does not invent a 292-bitplane bound.
Its existing checked multiply/add is one verified production helper over every
native `u16`, with unchanged field commits. Header validity is not a premise.

The internal contribution entry is not transactional: work charging can precede
a later arithmetic error, and a taken retained record need not be restored on
replay failure. These Tier-1 results alone do not establish outer clone/commit,
body/pass-total joins, packet/header associations or the public mixed dispatcher;
the next actual packet stage closes the selected code-block caller boundary.

The next actual packet stage is now in [packet.rs](packet.rs). Its sole raw
contribution projection includes every public field, the stored count and both
complete 164-entry arrays. Real descriptor lookup, checked body subranges,
actual legacy contribution execution and ordered pass/offset/index commits
form the complete legacy packet-body model. Final consumption/pass-total
errors occur after decoder effects, not before them.

Shared preparation models actual length/route/zero-setting admission. On the
actual legacy selector `!contribution.high_throughput`, the staged and public
packet-body callers now have complete Result/full-state refinements through the
actual faithful whole-decoder Clone. Staged errors can expose partial work;
public errors roll back every decoder field. This profile predicate selects a
real format branch only: it adds no header validity, geometry, normalization,
success, budget or trace premise. The HT packet branch and whole packet/header
association remain separate integration obligations, not guessed outcomes.

## Native container and selection output reading path

Start at `part2_validate_selection`: checked native geometry, exact explicit
tile sequence admission, bounding rectangle and row-major membership, actual
region and ordered intersection selection. `part2_color_selection_requested`
then composes the actual validation result with every reduced target value and
sampling/registration-context update. Targets and regions are whole sequences,
not opaque array identities. Native malformed counts, zero subsampling,
overflow, saturated expansion and discard rejection remain results, not
normalization or adequate-budget premises.

`part2_associated_codestream_header` denotes the actual parsed/fallback/missing
header choice and offset. `part2_validate_selected_header` preserves native
uniform/variable depth checks. `part2_apply_associated_output`,
`part2_convert_associated_selected` and
`part2_finish_associated_selected_output` connect the real supplied typed
image/header to complete mapping/admission/color/crop values and ordered errors.
None identity and missing-header behavior are distinct. These are actual
runtime producer boundaries on native parsed metadata/typed objects, not an
uninterpreted or successful decoder/header trace. F8 still must compose the
earlier compressed parser/entropy/reconstruction chain and frame results.

## Frozen full F5H refinement-plane profile

The continuing stage is the entire actual `decode_ht_refinement_plane`, for
both one and two refinement passes and every native pass/bitplane/cap input.
Initial rejection and complete duplication precede reader construction and the
cleanup-significance snapshot. Two passes execute reverse magnitude refinement
first, then forward significance propagation. All six raw words and flags,
both physical readers, complete claimed/stuffed vectors, every statistic and
the separate evolving discovery plane/pending sign coordinates are observed.

Significance discovery follows actual four-row stripes and four-column patches,
including vertical-causal neighbor suppression. Discovery writes precede delayed
per-patch sign reads and output stores; discovery signs are not silently replaced
with output signs. Final claim/padding/stuffing/collision/work rejection follows
all stores. Each first-error partial state and transactional boundary must match
the real producer. No valid-plane, normalized-coefficient, valid-stream,
successful-decode or adequate-budget premise is introduced. Private geometry
bounds must follow from the real duplicate checks. An additive-only, one-pass or
reader-only result is not completion of this full S+R profile.

The completed caller boundary includes both the unconditional inner symbol
caller and actual `decode_high_throughput_segments` byte entry. All native style,
pass counts, retained state and three real owner caps are admitted. Public pass
and significant-bitplane preflight occurs before the real byte parser; byte and
work admission then precede the inner caller. Inside that caller, actual metadata
still precedes pass conversion. Neither order is transplanted onto the other.
`None` and `Some(empty)` retain different pass/segment/refinement-state effects.
Inner failures can clear retained refinement data before rejecting a refinement
segment, while later accounting overflows retain prior committed fields.

The private reader constructor wrapper was removed after the production entry
began calling its existing shared verified free implementation directly; its one
test uses the same implementation. No public API or second executable decoder
was introduced. Pending sign vectors are still allocated once per actual patch
and dropped at the original patch-iteration boundary. Magnitude operations use
the real owner contracts, including complete native subtraction and zero.
Continuation/empty replay, placeholder skipping, replacement orchestration and
mixed HT/legacy routing remain outside this completed entry profile.

## Earlier cleanup-only symbol-caller subprofile

The earlier bounded caller profile was the **cleanup-only** branch of the actual
`Tier1CodeBlockDecoder::decode_ht_coefficient_symbols`: the supplied parsed
segment has `refinement == None`. This is an explicit format-profile selection,
not a valid-stream, normalized-coefficient, successful-decode or budget premise.
The real metadata producer's result feeds the real numerical reconstruction;
metadata is not a theorem input. Metadata decoding precedes pass-to-bitplane
conversion and subtraction. Reconstruction and the complete cleanup-plane
duplicate precede clearing retained refinement bytes/passes. Plane/stencil/
reader rejection therefore leaves the entire decoder unchanged. The final
assignments precede checked set/pass/segment/byte accounting, so a later overflow
can expose earlier committed fields. Every decoder field, including untouched
legacy/MQ/bitplane state, must be framed.

The shared cleanup preparation and final state-store stages remain unconditional
over their native inputs. The earlier caller theorem selected absent refinement
only; it did not assume a refinement trace. The complete current refinement and
substantive public-byte profiles above now subsume this subset and provide their
own unconditional production relations. Continuation/replay, placeholder
skipping, replacement/mixed sequencing and whole-decoder composition remain
separate closure obligations.

## Actual raw palette lookup

`part2_palette_value` uses the stored entry count, actual physical column
descriptor sequence and actual physical signed-value sequence. It first checks
whether the physical column count fits `u8`, then the logical entry/column
coordinates, then the checked `usize` row-major address, then actual value
presence. A physical value outside the logical table is not a valid lookup;
truncation inside it returns `InvalidBoxContents`. Column-count/address overflow
returns `ArithmeticOverflow`, with offset zero. The common existing
`part2_composition_error` denotes these same two error values; it adds no
composition premise.

This deliberately models the raw lookup, not the parser's palette-shape rules
or the mapper's precision/sign/sample-index rules. The raw operation returns the
stored `i64` unchanged, including both extrema, and ignores descriptor
precision/sign. Its complete actual production relation is unconditional on
stored shape and native coordinates. Palette parsing, component mapping and
their composition remain unproved by this raw lookup result alone.

### Complete component copy and palette interpretation

`part2_typed_component_copy` preserves all input fields and the ordered CDEF
sequence without adding geometry, precision or sample-tag validation.
`part2_palette_component` instead changes precision/sign from the actual
selected descriptor and starts with empty CDEF. It preserves the source's
width/height, subsampling and registration even when those fields are malformed.

The precision variable is the descriptor's bit count, restricted by the actual
body to 1..38. `part2_palette_modulus` denotes the same power of two; explicit
bit-vector facts relate its original multiply-by-two loop to the existing
`part1_output_minimum`/`part1_output_maximum` signed/unsigned range functions.
Source indices are interpreted independently of source precision/sign metadata.
They must fit the native 16-bit palette index and stored logical entry count
before `part2_palette_value` checks physical storage.

`part2_palette_samples` is the ordered whole-sequence denotation, including the
first failing sample. Its prefix is essential result semantics, not a separate
execution trace premise. Empty samples still reject an invalid descriptor but
do not trigger physical-column-count/table/entry failures absent from the
executed body. The actual full result also contains the output sample tag and
all metadata. Whole-header cmap selection, CDEF routing, typed-image admission,
parsing and selected-pixel joins remain outside these component results.

### Complete supplied output header and image admission

`part2_apply_output_header` composes actual ordered component selection and
palette interpretation, actual ordered CDEF append, and
`part2_typed_image_from_parts`. `jp2::output_header_view` projects the actual
palette/mapping/definition vectors consumed by the executable body, not the
stored count hints or unused image/color metadata. Empty CMAP copies every
source. No well-formed-header, matching-shape, successful-lookup or
adequate-budget condition is imposed. The recursive mapping/definition folds
give sequential first-error semantics; the production proof supplies the
actual vector states rather than accepting an execution trace as input.

Final admission checks origin addition, u16 component-count conversion,
actual component cap, and each component's area/sample count and cumulative
eight-byte charge. `part2_typed_image_admission_prefix` retains the first
failing admission even when later components have other defects.
`part2_typed_image_component` distinguishes the real image-index error from
the header's container-mismatch errors. Output geometry, sample values/tags,
metadata and all ordered CDEF records are included. Unread native fields are
deliberately not validated. Parsing, header association and selected target
composition remain separate obligations.

## Frozen F5H cleanup-plane reconstruction profile

The next full numerical boundary is the actual `reconstruct_ht_cleanup_plane`,
not a validated-metadata wrapper. It admits arbitrary stored quads, dimensions,
initial-row flags, masks, coordinates, U values and native bitplane/work limits.
Only metadata width is checked before creating the blank output using the input
plane's dimensions; old input coefficients are ignored. Coordinate addition
precedes metadata clipping. Scanning precedes MagSgn consumption, which precedes
placement and both success counters. Duplicate or out-of-output placements can
therefore fail after consuming a magnitude. All six stored words, flags,
statistics, both exponent stencils and every reader field are observed by the
shared production stages, including their first-error partial states.

Column-zero reset, sample-one maximum, sample-three overwrite and end-of-row
stencil swap follow actual metadata vector order, not assumed geometric order.
Noninitial kappa retains its conservative base-plus-exponent overflow check.
No-significance, empty or fully clipped metadata does not impose numeric-domain
checks absent from the body. Final physical padding, stuffing and work errors
remain after all placements. This profile does not establish refinement,
placeholder/replacement/mixed routing or complete entropy conformance.

The raw `Tier1CodeBlockDecoder::plane` postcondition is an existing API bridge
consumed by `decode::prepare_tile_component_with_kernel`. It remains outside the
same-file internal-caller index: there is no invented Tier-1 caller or generic
API-root exemption. Its exact view is listed as a proof reference.
The raw and signed `Result` projections are open over their public payloads and
closed owner views, so outside-module consumers can connect actual returned
fields to the mathematical result without revealing private stored fields.

## F6 reconstruction profiles (bounded stage contracts)

The first F6 stage starts with supplied signed 384-bit magnitudes (six
little-endian `u64` limbs), not compressed bytes or Tier-1 meaning. It covers
every ROI shift in `u8`, both quantization modes, the full coefficient sequence,
and the returned one-row plane's samples, width, height and fraction bits.
The integer-input adapter must reject `i64::MIN` before validating quantization
parameters or the decoded-byte budget, as the production call order requires.
The magnitude path validates parameters, then the eight-byte-per-sample budget,
then samples in order, and finally the `u32` width. Restored magnitudes must fit
`i64::MAX`, including for negative inputs; this is not a normalization premise.
Irreversible results describe the implementation's integer Q16 arithmetic,
including zero-sized steps after truncation, not real-valued 9/7 conformance.

The second bounded profile is the entire `inverse_5_3` sequence: geometry
validation and interleaving, symmetric boundary extension, both lifting
passes, either low-pass parity, empty input, and the high-only singleton's
arithmetic right shift. Every `i64` input is admitted to the relation; checked
neighbor-sum, update-bias and sample arithmetic determine typed rejection,
not an assumed coefficient bound. The shared lifting contract also describes
the complete partially modified buffer on failure, retaining all untouched
positions. The entire `inverse_9_7` sequence is also contracted: interleaving,
the two parity scaling passes and all four ordered lifting passes, including
their actual Q16 constants, checked intermediates and unchanged singletons.
Scaling and the four-stage coordinator retain complete failure buffers.
This is an integer implementation model, not real-valued 9/7 conformance.

The horizontal, vertical and single-level two-dimensional 5/3 and Q16 9/7
entry points have complete plane Result contracts. Their production row and
column coordinators are shared with the actual level implementation; there
is no second executable transform. No successful-result, coefficient-bound or
budget premise is imposed on these public contracts. Internal conditional
contracts select the standard-kernel profile (`kernel == None`); arbitrary
kernel meaning is not inferred from those conditions.

The existing geometry/error distinctions are intentional. Standalone
horizontal/vertical stages check dimensions and the output budget before
accessing band samples, and ignore unaccessed trailing samples. Horizontal
zero-width planes and vertical zero-height planes retain their existing
behavior. A full level instead rejects either zero output axis and validates
all four exact band sizes before its output budget. Zero-sized intermediate
low/high bands remain valid where the selected parity requires them.
Column storage models preserve every earlier write on a later failure.

The existing public `convert_samples` API also has complete ordered rounding,
level-shift, clipping and typed-error semantics. Its actual precision domain
is 1..38 with 0..62 fraction bits; rejected parameters are not preconditions.
It uses sample length, not plane dimensions, for its budget and deliberately
does not validate plane geometry. Checked rounding/level-shift overflow occurs
before clipping. This API is exercised by concrete consumer tests; it is not
the decoder's separate image/component conversion path.

The decoder's existing `DecodedComponent::typed_samples` and
`DecodedImage::typed` now have their own complete Result relations. They use
the actual F7 typed-sample, component, geometry and channel-definition views:
the result includes every signed/unsigned sample, all image/component metadata
and the existing empty output channel-definition lists. No typed/CDEF class,
getter, metadata definition or color conversion is changed or duplicated.
The original loops use the same actual scalar rounding/clipping stages.

Their domains and order differ from the separate transform conversion API.
Component conversion rejects precision outside 1..38 before its sample-length
byte budget. Image conversion instead charges the cumulative eight-byte count
before calling each component, so that budget error precedes that component's
precision error. Fraction values above 62 reject only when a sample is read;
empty valid-precision components therefore retain success even with arbitrary
fraction bits. Checked rounding bias and unsigned level shift may overflow
before clipping. Dimensions, subsampling and registration are copied as raw
metadata, not assumed valid or newly validated. Prefix models preserve the
first error through the entire sample/component sequence.

The actual free reversible and fixed-Q16 irreversible component transforms
have complete mutable `DecodedImage` state relations. Their shared production
loop checks the existing first-three-component compatibility and sample
lengths, then transforms samples in order. All `i64` triples are admitted;
checked sum/product/bias/addition failures determine rejection. Every image
and component metadata field, sample length and component beyond the first
three is preserved, including on failure. The previously completed sample
prefix remains committed when a later pixel fails. These functions do not
add a plane-area consistency or precision/registration policy absent from
their existing compatibility checks. A closed `View` covers all decoded
fields; it does not reuse or alter F7's typed/CDEF structures.

Raw kernel/step/coefficient views and exact getter contracts expose only the
actual consumed representation fields, including all coefficient bytes and
the recorded width. They impose no parser validation or normalization facts
and do not by themselves prove an arbitrary-kernel algorithm.

The actual read-only `PacketPrecinctDecoder` decoder/count/slice accessors
expose a public closed projection of the complete private decoder Vec.
The indexed Result covers every `usize`, returns the exact initialized entry
or `MalformedInput { offset: 0, kind: InvalidPacketHeader }`, and makes no
assumption that the parallel packet-state/context vectors have matching shapes.
This raw representation interface does not assign entropy or packet meaning.

The real quantized-block write loop in
`decode::prepare_tile_component_with_kernel` now calls one shared verified
production block/row/pixel implementation. Its complete working-subband state
model includes width, height, fraction bits, samples and the entire visited
mask. Source/destination/mask length mismatches, previsited cells and checked
coordinate/index errors retain all prior writes. Metadata and buffer lengths
remain unchanged; marked cells never become unmarked and previsited sample
values are protected. No rectangular-shape, prevalidated-buffer or sufficient
length premise is imposed on this transition. The caller's earlier geometry,
coefficient extraction, quantization and fraction checks remain in their
original order; this theorem does not silently replace those checks.

Both actual image assembly entry points now have unconditional complete Result
relations: `assemble_image` and the active `assemble_selected_image`. They fold
the supplied tile samples into every component and preserve all image and
component metadata. Registered geometry uses the actual Q16 registration
coordinates. Cumulative decoded-byte accounting, physical component-info bounds,
raw fraction consistency, overlap, missing coverage and arithmetic errors retain
their original order; neither valid headers nor sufficient budgets are premises.
The real production code shares component, tile, rectangle, row and pixel stages,
whose mutable views include every sample and visited flag on failure.

Base and selected assembly intentionally have different domains. Base assembly
rejects zero tile axes and requires the exact tile area. Selected assembly checks
matching tiles' fractions and overflowing extents even off-region, but copies
only their intersection: samples outside that intersection need not exist.
Wrong-component tiles are ignored, and selected missing coverage has its distinct
selection error. Budget checking remains before selected crop-offset arithmetic.
Zero axes/counts and arbitrary fraction values retain their native behavior.
Only the inactive nested selected-assembly duplicate was removed; the theorem
links the actual active caller, not that dead copy.

`ImageSize::component` and the three reconstruction direction/count selectors
also expose complete Results over their full native `u16`/`u8` domains. Raw
component counts and decomposition levels are not assumed to fit the physical
64/32-entry arrays. These interfaces do not establish parser validity.

The actual public `prepare_tile_component` now has a complete unconditional
Result relation for its standard **None-kernel** call path. The same private
`prepare_tile_component_with_kernel` body now additionally has the complete
unconditional `part2_prepare_component` relation for actual None/Some inputs.
The standard result is an exact None wrapper, not a weaker parallel semantics.
Every actual raw plan/precinct/decoder/plane/coefficient field, style selector
and cap is admitted. An Arbitrary transform with no kernel rejects exactly.
No valid header, normalized coefficient, covered band, successful callee,
adequate budget or supplied execution trace is an entry premise.

The production coordinator shares its real initialization, collection,
placement, coverage and resolution stages. It checks the selected band count
before initializing bands, charges nine bytes per sample cumulatively before
allocation, checks block geometry before collecting coefficients, reads the
actual row-major raw coefficients with full 384-bit signed/midpoint semantics,
then invokes the actual ROI/quantization and checked sample/mask writer.
Unselected placements remain ignored. Coverage precedes reconstruction.
The entire fold supports arbitrary native resolution selectors, None/H/V/2D
directions, per-stage parity, the actual integer 5/3 or fixed-Q16 9/7 algorithms,
ordered detail indices, output budgets and cursor errors. Final dimension,
sample-count, component, origin and fraction fields are related exactly.
The real prepared-to-tile getter also preserves every field/sample.

Only derived private append-loop structure bounds are used to discharge a
Vec-push precondition; they are proved from initialization and never imposed
on the public plan input. Complete working-state views include all bands'
metadata/samples/visited flags and the byte counter on failure. Independent
whole-plan tests reuse the existing widened integer/rational transform oracles,
not the production transforms, with nonzero completed one-bit input blocks,
mixed/multilevel directions, parity, reordered and ignored placements and
ordered malformed/resource cases.

The arbitrary reading path starts at `part2_inverse_arbitrary`, then scaling
and the reverse-step/target folds. All native flags and raw coefficient bytes
are included, even contradictory descriptors or width hints that the body does
not validate. `part2_atk_fixed_coefficient` covers integer and raw binary
32/64/128 formats; binary ties-even conversion and the existing right-shift
cutoff are distinct from signed lifting bias and native truncating Q32
division. The target fold preserves all already written samples on error.
Singleton half and unvisited defects retain their actual bypass behavior.

`part2_kernel_inverse_horizontal`, `part2_kernel_inverse_vertical` and
`part2_kernel_inverse_level` select the actual supplied kernel or standard
algorithm. `part2_prepare_resolution` still checks the resulting fraction
against the style-derived expectation after execution, not as an input
agreement premise. The generalized fold/reconstruct/component definitions
share every earlier raw collection/placement/coverage/budget stage. Original
standard names delegate to precisely the None case. Independent raw-context
and arithmetic regressions supplement the full production proof; inventory
and frozen numerical/resource qualification are not presumed from it.

`part2_mct_round_shift` and `part2_mct_rescale` denote actual MCT signed
rounding and every native precision pair; they are not the arbitrary-kernel
lifting-bias operation. Raw MCT array views bind metadata and full values,
including metadata contradictions the row body does not inspect.
`part2_mct_row_initial`, `part2_mct_dot_term`, `part2_mct_dot_prefix` and
`part2_mct_matrix_row` give complete actual reversible/scaled matrix-row
results and first errors. Optional offset, scratch and work-charge models
include native malformed states and exact partial counter writes. The owner
Q32 identity is proved rather than treating the private constant as a new
assumption. These arithmetic/row results do not establish collection/stage
dispatch or dependency/wavelet orchestration.

These row models alone do not establish collection or stage dispatch. See
[complete native MCT composition](../PROOFS.md#complete-wavelet-stage-and-real-owner-buffer-mct-composition)
for the additional actual producers. Raw-input-to-component-sample
composition, independent unavailable-reference adjudication, parsing and
entropy-decoding boundaries must still be reviewed separately.

### Reconstruction reading path

1. `part1_magnitude_*` defines six little-endian limbs, lexicographic magnitude
   comparison and cross-limb logical shifting. These are finite bit-vector
   denotations on all 384 bits, not an assumption that coefficients already fit
   a machine sample.
2. `part1_roi_coefficient`, `part1_quantization_step` and
   `part1_dequantized_sample` specify restoration before narrowing, Q16 step
   truncation, centered scaling and checked signed output.
3. `part1_quantized_prefix` fixes sample order and first-error absorption.
   `part1_inverse_quantization` adds parameter validation, budget checks and
   complete plane metadata. `part1_inverse_integer_quantization` adds the
   integer adapter's earlier `i64::MIN` rejection.
4. `part1_interleaved`, `part1_lifting_sample`, `part1_lifting_prefix` and
   `part1_inverse_five_three` specify full sequences and mutable lifting states.
   `part1_scaling_prefix`, `part1_nine_seven_lifting_prefix` and
   `part1_inverse_nine_seven` add the complete fixed-point sequence.
5. `part1_band_row`, `part1_column_prefix`, `part1_store_column_prefix`,
   `part1_horizontal_prefix` and `part1_vertical_prefix` fix extraction,
   concatenation, row-major storage, first-error order and complete buffers.
   `part1_inverse_horizontal`, `part1_inverse_vertical` and
   `part1_inverse_level` add actual geometry, budgets and plane metadata.
6. `part1_round_fixed`, `part1_conversion_prefix` and `part1_convert_samples`
   describe the existing public final-sample conversion API.
7. `part1_component_values`, `part1_component_pixel_state`,
   `part1_component_transform_prefix` and `part1_apply_component_transform`
   give the actual complete decoded-image component-transform relation.
   `part1_component_transform_frame` states its complete metadata/extra-plane
   preservation property, not a substitute for sample semantics.
8. `part1_quantized_block_pixel`, `part1_quantized_block_row` and
   `part1_quantized_block_rows` describe the actual coefficient write stage,
   including samples and visited flags. They do not establish the entire
   `prepare_tile_component_with_kernel` result simply because its callees
   now have contracts.
9. `part1_assembly_pixel`, the row/rectangle/tile/component prefixes and
   `part1_assembly_append_plane` describe the shared real assembly stages,
   including complete write masks and ordered byte accounting.
   `part1_assemble_image` and `part1_assemble_selected_image` close the actual
   full image entry points relative to supplied tiles, not supplied coefficients.
10. `part1_decoded_signed_prefix`, `part1_decoded_unsigned_prefix`,
    `part1_decoded_component_typed_samples`, `part1_decoded_typed_components`
    and `part1_decoded_image_typed` give the existing decoder conversion's
    complete sequence, metadata, empty-CDEF and first-error relation.
11. `part1_prepare_init_prefix`, coefficient row/plane and placement prefixes,
    `part1_prepare_coverage`, `part1_prepare_resolution` and `part1_prepare_fold`
    compose the real standard coordinator. `part1_prepare_standard_component`
    and `part1_prepare_finish` close the actual public Result, not a surrogate
    coordinator or a theorem assuming the callees succeeded.

All prefixes here are algorithm denotations, not invariant-only witnesses.

### Full native magnitude interface

`magnitude::magnitude_value` is a public **closed** natural-number view of all
six little-endian `u64` limbs, defined by `part1_magnitude_value`; it is not a
low-word surrogate. Capacity is `part1_magnitude_capacity() = 2^384`.
The existing raw `magnitude_limbs` view and ROI contracts remain available.

The original receiver operations have full native-domain contracts:

- `checked_add`: exact natural sum below capacity; otherwise precisely
  `MalformedInput { offset: 0, kind: ArithmeticOverflow }`.
- `checked_sub`: exact full-384-bit natural difference iff the first operand
  is at least the second, including successful zero for equality. Every
  underflow returns the same exact arithmetic error. Raw/value/shape/capacity
  agreement is exported with no no-underflow or positive-result premise.
  The original native borrow algorithm, including an incoming borrow across
  a `u64::MAX` subtrahend word, is unchanged. A prefix-order proof connects the
  existing lexicographic guard to natural order, and subtraction reuses the
  proved carry algebra with the operands rearranged.
- `checked_shl`: exact multiplication by `2^shift` when representable, for
  every `u16` shift. Zero succeeds even for shifts at least 384; nonzero
  values reject there. No HT-only success premise is imposed.
- `shift_right`: floor division by `2^shift`, including zero at shifts
  at least 384, with the complete raw-buffer relation retained.
- `low_u64`: full-value modulo `2^64`; `is_zero`: true iff the full value is
  zero. The numeric/raw representation agreement and intrinsic capacity
  bounds are exported by these contracts.
- `limb`: for every native `usize` index, exactly the corresponding raw word
  at indices 0..6 and `None` otherwise, with no index precondition.

The public pure owner fact
`magnitude::representation_proofs::magnitude_limbs_shape(value)` establishes
`magnitude_limbs(value).len() == 6` without an executable getter call.
Its small representation proof submodule stays under the owning module so
the existing public closed projection and private fields remain closed;
the indexed mathematical denotation is `part1_magnitude_limb` in `specs/mod.rs`.

Verified native producers are `magnitude_zero`, `magnitude_from_u64`,
`magnitude_from_limbs` and `magnitude_single_bit`. The zero helper returns
exactly the existing `Magnitude::ZERO`; the bit helper accepts the entire
`u16` domain and returns the exact arithmetic error at bit indices at least
384. Existing public associated factories retain their API and delegate to
these same implementations. Verified internal callers should use the free
factories because the pinned conditional-attribute frontend cannot infer
associated static-function contexts; no trusted specification compensates
for that limitation.

Only the partial native left-shift buffer witness is in
`proofs/internal_specs.rs`. Full value, shift and overflow denotations remain
on this reading path; their word-composition, carry and natural arithmetic
lemmas are proved in the production proof module. Native optimized limb
algorithms remain in `src/magnitude.rs`. Independent bit-array tests cover
every `u16` shift/bit index and complete 384-bit carry propagation.

The executable cores `inverse_quantize_values` and `inverse_quantize_plane`
take an explicit decoded-byte budget. The original `inverse_quantize` and
`inverse_quantize_magnitudes` entry points additionally have complete Result
contracts using `resource_decoded_bytes_limit`: the actual getter is proved
equal to that closed private-field projection. No width, pixel or work-unit
policy is silently added to this stage.

This directory contains the semantic models used by production contracts.
It is an audit entry point, not a claim that every selected standard clause
has been reconciled or proved.

## Reading path and reference status

1. Read the selected editions and acquisition boundaries in
   [REFERENCES.md](../REFERENCES.md).
2. Use [normative-coverage.json](../validation/normative-coverage.json) to locate the
   implementation, model, contract, proof and independent test for a topic.
   This is a technical index, not an exhaustive clause checklist.
3. Compare the semantic definitions in [mod.rs](mod.rs) with the authorized
   reference, then inspect their actual production contracts under [src/](../src/).
4. Read representation/induction details under [proofs/](../proofs/) as needed.
   The established and unestablished relations are listed in
   [PROOFS.md](../PROOFS.md#concrete-contract-boundaries).

| Reference | Model entry points | Audit distinction |
|---|---|---|
| T.800 (2024-07), core coding/JP2 | `part1_*`, marker/packet, geometry, MQ and transform models | Check encoded field widths, sample precision, signedness, coordinate grids and arithmetic domains against the selected reference. |
| T.801 (2023-08), extensions/JPX | `part2_*`, ADS/ATK/NLT/CBD and composition models | Some syntax interpretation used acquired T.801 (2021). The selected 2023 reconciliation still requires authorized text; no missing clause numbers are invented here. |
| Selected normalized composition profile | `part2_layer_input`, `part2_owned_layer_input`, `part2_source_over_pixel`, `part2_composition_geometry`, `part2_composition_layer_transition` | Normalization to 16 bits, channel/alpha construction, floor-scaled sampling, checked addresses, typed errors and work limits are explicit selected implementation policies, not blanket claims about all JPEG 2000 profiles. |
| Supplied composition metadata and normalized layer results | `part2_build_timeline`, `part2_select_frame`, `part2_render_normalized_frame`, `part2_render_layers`, `part2_image_from_planes` | Whole timeline construction and complete indexed-layer-result-to-frame rendering are input-relative theorems. Compressed decoding and container interpretation/normalization are not proved by these models. |
| T.808 (2026-06), JPIP | `part9_*` and databin/range models | The cited catalog record is not an acquired normative text or a completed edition audit. |
| T.814 (2019-06), HTJ2K | `part15_*`, `valid_ht_*` and HT cleanup/refinement models | Separate coding semantics from implementation capacity bounds and generated-image qualification. |

For a clause-level review, record the authorized edition/clause, its variables,
units and ranges beside the corresponding model and evidence. The unresolved
edition boundaries above must remain unresolved until the authorized source
is available; a successful solver run does not fill them in.

## HT directional-reader contracts

The raw Tier-1 observation substage retains every stored coefficient limb,
legacy midpoint tag and sign/significance/refinement flag. Plane dimensions
and the actual coefficient sequence are not normalized to a rectangle:
coordinate bounds, native checked address arithmetic and actual sequence
length determine the exact indexed result/error. Signed observation ignores
stored bits/tags when insignificant, otherwise applies the actual full-native
legacy midpoint and checked overflow branch without entropy or normalization
premises. It is a raw producer interface, not coefficient reconstruction.

The frozen numerical MagSgn substage is the actual complete
`reconstruct_ht_magnitude` operation for every native completed-U,
embedded-bit/value flag and decoded-bitplane input, with every initial
directional-reader state admitted. Original parameter rejection precedes
any read. The exact result includes the full 384-bit numeric value, sign,
exponent and every final reader field on success or first error. Accumulation,
embedding, odd-center correction, centering, checked left scaling, right
division and zero rejection use the real published F6 contracts. No stream
validity, sufficient budget or successful arithmetic/read is assumed.
This substage is numerical reconstruction, not complete plane placement.

The frozen cleanup-metadata stage is the complete actual segment traversal,
not coefficient reconstruction. Inputs retain all native width, height and
maximum-U values, the actual supplied segment views and actual work limit.
Header checks, reader construction, ordered rows/pairs/members, north/west/
east context selection, context-zero suppression, UVLC/event decisions,
sample bounds, significant-sample counting, quad stores, ticks, final collision
check and counter conversion are part of one deterministic result model.
Every output metadata field and typed first error is included. Internal
geometry/allocated-length facts are proved from the real header checks;
neither valid streams, successful reads nor sufficient budgets are assumed.
Helper extraction moves the existing traversal bodies, without another
executable decoder, changed allocation capacities or reordered stream reads.

The packet-pass grouping substage has the native `u8` input domain: zero and
165..=255 reject, while 1..=164 produce the exact cleanup-pass count,
refinement-pass count, placeholder count and skipped-bitplane count.
All four actual result fields and the typed rejection are modeled. This is
the actual `HtPassGroup::from_packet_passes` implementation, not a theorem
that a block caller executes, replaces or routes those passes correctly.

The frozen byte-partition contract uses the actual selected code-block
byte limit, not a chosen or existential budget. Its inputs are both
actual supplied slices (including `Some(empty)` versus `None`), all native
lengths and the actual `ResourceLimits` object; its output includes every
encoded/substream slice, offset and direction. The current foreign limits
getter now has the specifically authorized owner-local limit view and exact
postcondition. Cleanup/refinement size rejection precedes the code-block
budget check, which precedes Scup interpretation. Every encoded/substream
slice, offset, direction and total byte count is included. Invalid Scup
bounds retain their typed rejection. No arbitrary-budget parser wrapper,
successful-input assumption or narrowed native object domain is substituted.

The next frozen interpretation substage is the actual cleanup UVLC/quad-word
caller: prefix, every native `u8` suffix length, combined prefix value,
initial/non-initial U pairs for every `u8` mode, and quad-word lookup for every
`u8` context. It composes the actual reader/event/advance/tick states on every
return. Invalid modes/contexts reject without consuming; a set suffix bit
above bit seven rejects **after** that bit is consumed, while zero bits above
the result width may continue. Initial mode three preserves its special
long-prefix route and read order; bias one/three and checked byte conversion
retain their actual rejection points. Quad lookup uses closed views of the
unchanged production tables, then context-zero MEL suppression, length
validation, actual advance and final tick in that order. This stage does not
assume valid codewords, available bits, adequate budget or valid counters.
It is not a quad traversal or coefficient-reconstruction theorem.

The next frozen substage is the complete actual MagSgn reader API: construction
from 0..=65534 bytes; LSB-first words of 0..=39 bits and unchanged-state rejection
of larger counts; physical and synthetic `0xff` bits with forward stuffing;
all physical/fill/work counters and cursor fields; and `finish`'s exact
bounded drain, padding-one rejection and first typed failure. All native
counter values remain admitted. Cursor advancement precedes selected-counter
charging, which precedes work charging and the work-limit check. The finish
fuel is the checked native-width product `input.len() * 8`, including its
overflow error before testing whether physical bits remain. Neither a valid
stream nor enough budget is assumed. The word and drain recurrences belong
to the semantic reading path, not to invariant-only support.

The following frozen substage is both actual refinement directional readers
and their shared claim/padding wrapper. Each input accepts 0..=2046 bytes.
Forward reads supply zero fill after physical data; reverse reads begin with
unstuffing enabled and supply zero fill after exhaustion. Positioned reads
report the actual native-width byte/bit position, then advance the cursor,
charge the selected physical/fill counter, check their sum for overflow and
check the work cap. Counter errors and budget errors preserve those ordered
partial mutations. The wrapper records successful physical claims, rejects
repeat claims, records reverse stuffed-bit masks at the actual loaded byte,
and checks all unclaimed/unstuffed padding bits at finish. Models include both
complete readers, optional reverse-reader absence and both complete vectors.
No successful decoding, sufficient budget, disjoint claims or valid padding
is assumed.

The next frozen cleanup-caller substage includes the complete actual VLC
`peek_vlc` and `advance_vlc` APIs for every `u8` count, and `mel_event` for every
native cache/state/counter value. Peek is non-mutating and returns the word
accumulated before copied-reader exhaustion, collision, budget/overflow
failure or a set bit above its 16-bit result capacity. Advance stops at the
first actual read failure with its full nested state retained. MEL cache
priority, 0..=12 state validation, head/suffix consumption, state adaptation,
termination caching and event-counter overflow are explicit, including
partial suffix-reader mutations on failure. Event suffixes are MSB-first.

The first finite subprofile is the actual cleanup MEL/reverse-VLC reader pair:
MEL accepts 1..=4078 bytes, reverse VLC 2..=4079. Contracts cover constructor
rejection, exact loaded bytes and returned bits, terminal-nibble handling,
directional stuffing, exhaustion, positions, all final fields, counter overflow,
and the first work-limit failure. Counter domains retain the full `u64` range;
failure is not assumed absent. Reverse VLC eagerly loads the previous byte only
after charging a successful bit; budget rejection therefore preserves its old
loaded byte with an advanced bit cursor. MEL exhaustion sets its cursor to -1.
The pair's actual `read_mel_bit`/`read_vlc_bit` wrapper includes shared-byte
claim/collision rejection and both inner and outer work counters. All nested
reader fields and MEL event fields are framed, including failed reads after
loading and failures after recording a successful byte claim. Constructor
order is MEL, then VLC, then terminal-byte setup. The model accepts the actual
supplied slices; it does not assume they were partitioned correctly upstream.
These are selected implementation-state relations, not a human normative
endorsement of T.814.

The directional substage now includes all five actual readers, MagSgn words
and finish, refinement physical-bit claims/padding, VLC peek/advance and MEL
events. The cleanup pair's final shared-byte collision check is included.
The subsequent UVLC/quad-word interpretation stage above is also complete.
Actual upstream partitioning and the complete metadata traversal above are
now proved. The remaining stages are pass execution/sequencing, numerical
cleanup magnitude/coefficient reconstruction, significance/refinement
block transitions, replacement/placeholder sequencing and mixed HT/legacy
routing. Completing directional stages does not close F5H or full-block
acceptance. In particular, matching the byte-reader state machine does not
prove that the block caller requests the right symbols or reconstructs the
right coefficients.

## Normalized source-over vocabulary

These symbols describe the selected composition stage, not the original
codestream component precision:

| Symbol | Definition and range |
|---|---|
| `p` | `PART2_NORMALIZED_SAMPLE_BITS = 16` |
| `M` | `PART2_NORMALIZED_SAMPLE_MAX = 2^p - 1`, represented by `u16::MAX` |
| `h` | `PART2_NORMALIZED_SAMPLE_HALF = floor(M / 2)` |
| `Cs`, `Cd` | Source and destination color samples, in `[0, M]` |
| `As`, `Ad` | Source and destination alpha samples, in `[0, M]` |
| Premultiplied source | Every active `Cs <= As`; absence of source alpha means opaque straight samples |
| `A` | Unbounded natural alpha numerator: `As*M + Ad*(M-As)` |
| `C` | Unbounded natural color numerator: `Cs*As*M + Cd*Ad*(M-As)` for straight source, or `Cs*M*M + Cd*Ad*(M-As)` for premultiplied source |

Output alpha is `floor((A + h) / M)`. Output color is zero when `A = 0`;
otherwise it is `floor((C + floor(A/2)) / A)`. Positive-denominator rounding
is nearest-integer with upward ties. Arithmetic models use natural numbers;
production checked conversions and their bounds are proved separately.

The domain and presentation equivalences are checked by
`normalized_composition_domain_matches_binary_width` and
`symbolic_source_over_matches_word_normalization` in
[proofs/spec_properties/mod.rs](../proofs/spec_properties/mod.rs). These relate
the named mathematical quantities to the prior word constants; they do not
replace an independent standard-edition audit.

## Semantic definitions versus internal proof support

`ht_cleanup_plane` and its sample/quad/finish models describe complete actual
cleanup coefficient reconstruction from supplied metadata and bytes, not
merely a scalar magnitude. Read counter/read/store ordering and both exponent
stencils alongside the actual final reader termination. Raw Tier-1 models
preserve all six limbs, significance/sign/refinement and legacy midpoint
behavior without assuming a well-shaped plane or normalized coefficient.
The small `tier1_raw_plane_*`, `tier1_coefficient_*` and `tier1_set_magnitude`
denotations are complete field/record projections used by real producer
contracts; they do not introduce an alternate executable implementation.

`color_crop_image` describes the actual selected-output crop on a supplied
converted image. Its ordered checks preserve the zero-size, coordinate-
overflow and bounds error precedence. The whole-image identity shortcut is
explicit and does not silently validate existing channel lengths. Otherwise
the complete ordered channel/row/column denotations stop at the first checked
address or missing requested sample. All source metadata other than output
dimensions is retained. These definitions do not assume canonical color
channels or prove earlier region selection, palette interpretation or pixels.
The `color_crop_ready` invariant bundle is internal proof support.

`color_convert_selected` connects conversion and cropping at the actual
selected-output caller. Its input is the supplied typed image and requested
reference-grid target, not a precomputed converted plane. Conversion completes
first; only then are target-origin/extent subtractions checked with the
existing target error, followed by cropping. It does not model the earlier
algorithm that derived the requested target or decoded the typed components.

`color_convert_jp2` is the complete result denotation for the actual public
typed-component converter. Read `color_output_format`, `color_channel_layout`,
`color_validate_components`, `color_validate_output_size`, then
`color_convert_colors` and `color_append_alphas_prefix` in that order. Named
JP2 enumerations select grayscale, sRGB or sYCC; other enumerations and both
ICC methods have explicit typed rejection. Component validation and budget
admission happen before sample conversion. The three essential prefix models
specify complete ordered channels, sYCC planes and appended alpha; each
absorbs the first actual error. The output includes every image/channel field.
The input is supplied typed components and color metadata, not an assumed
compressed-decoder trace or a claim about how a container authored them.

`color_conversion_ready` lives in
[internal_specs.rs](../proofs/internal_specs.rs) because it only bundles
already established immutable facts across the production loops. It is not
an additional algorithmic assumption or normative rule. The byte cap view is
the actual private `ResourceLimits` field, not a default or chosen proxy.

`color_sycc_to_srgb` specifies the actual fixed-point pixel conversion over
every native `u16` luminance and `i32` difference pair. Its coefficients are
91881, 22554, 46802 and 116130 with denominator `COLOR_FIXED_SCALE = 2^16`.
Each delta is rounded separately, with exact half ties away from zero,
before the three output sums are clamped to `[0, 65535]`. The pure
`color_fixed_round` uses unbounded integers; `color_rounded_fixed` separately
retains the checked pre-division overflow boundary for arbitrary `i128`.
`color_image_difference` separately connects real component lookup and nominal
sampling to centered chroma scaling by `65535/(2^p-1)`, with the same signed
nearest/tie policy. Neither pixel theorem proves component/output-budget
validation or the entire color-conversion loop.

The requested sYCC converter also admits a borrowed row plan for unit-grid,
unregistered luma and congruent 2:1 horizontal chroma with 1:1 or 2:1
vertical sampling. `sycc_row_indices` connects the retained chroma row base
and shared clamped column to the existing component-index denotation.
`convert_sycc_row_pixel` preserves the scalar pixel Result, including Y,
Cb, then Cr error order: only a pair already read and normalized
successfully at the same source index is reused. The plan is checked
after the existing output reservations, creates no owner, and declined
plans use the generic pixel path. Alpha and native planar output do not
use this plan.

`color_channel_layout` describes actual typed-image/CDEF routing before sample
conversion. Its default path is used only when every component has no
definitions. The explicit ordered fold retains alpha kind/association,
permits a repeated identical component/color assignment, ignores unspecified
channels, and rejects conflicting components or invalid associations at their
first occurrence. Required-color completeness is checked last. The native
`usize::MAX` unset marker is explicit; it is not a valid assigned index from a
representable component sequence.

`color_normalize_component` is a full fail-fast plane denotation over supplied
typed integer components and target reference grids. `color_component_index`
uses fixed-point registration in units of 1/65536, registered ceil origins,
registered floor sampling and explicit edge clamping. Sample precision
selects nominal maximum `2^p-1`; signed samples are checked and translated
from `[-2^(p-1), 2^(p-1)-1]` before exact nearest/upward-tie 16-bit scaling.
The word-width facts are checked by `color_precision_binary_bounds`, not
implicitly assumed. All geometry/range/tag/missing-sample errors remain
part of the model. The prefix definition describes the first actual sampling
failure; it is not a sufficient-budget or valid-input-only theorem.

`part1_raw_reader_initial`, `part1_raw_reader_load`, `part1_raw_reader_read`
and `part1_raw_reader_termination` describe the complete selected raw-bypass
reader state and typed outcomes. Byte/bit order, stuffing, synthetic marker
padding, consumed-byte position and counter/error ordering belong on the
semantic reading path. Native fields retain their stated widths; the initial
sequence is constrained to representable slice lengths. These models do not
claim that callers choose the correct pass/segment or normative context.
The termination model distinguishes an empty, zero-work raw pass from
synthetic bits consumed from missing input, and recognizes the unconsumed
`0xff`/`0x2a` full-byte/stuffed-padding boundary.

`part2_layer_input` describes selection from supplied converted channels:
scan all channel kinds first, then check the area and required color planes,
then validate and combine alpha planes. Required colors are returned in slot
order, regardless of input order; red and gray share slot zero. Missing,
duplicate, out-of-range or incorrectly sized planes have explicit typed
rejections. Optional alpha is an **ordered fold** of
`floor((a*b + h)/M)` with a rounding step after each plane. It is not a single
product rounded once. One plane preserves its representation flag; two or
more produce straight alpha. Association validation and earlier normalization
are outside this stage's input-relative theorem.

`part2_render_layers` denotes rendering the **supplied ordered placements**,
not an execution trace supplied as an assumption. Its initial canvas is
transparent black, its output space is sRGB if any supplied layer is sRGB
(even an inactive layer), and its layer fold stops at the first failure.
Each step first charges that layer's complete nominal decoded size, checks
the supplied byte cap, then invokes the budgeted placed-layer transition with
the carried canvas and work counter. Canvas initialization contributes its
pixel count to work and its planar storage to decoded bytes. As in the actual
implementation, the initial byte charge is checked together with the first
layer, not separately. The complete image result includes dimensions,
precision, channel kinds/association, and every color and alpha sample.
`part2_image_from_planes` also specifies the production constructor's exact
shape errors, including the accepted zero-area case.

`part2_select_frame` selects a modulo frame for indefinite playback or a
bounded repeated sequence, with exact empty/out-of-range/overflow errors.
`part2_frame_instruction_sequence` concatenates persistent predecessors and
the current frame in table order, preserving every instruction field. Frame
table positions, not stored frame indices or timestamps, determine selection.
The current frame is included regardless of its persistence flag; a transient
predecessor is skipped without erasing older persistent frames. Each render
starts afresh, and looping does not retain the preceding loop's canvas.
Instruction-level persistence and `next_reuse` are preserved as input metadata;
their interpretation by `build_timeline` is not established by selection.

`part2_build_timeline` starts with empty frames/assignments/time and processes
each instruction set `repeat + 1` times. Its deterministic transition assigns
the next new layer unless an earlier instruction reserved this position for
reuse. It models exhaustion, zero-life grouping, persistence overwrite,
start/duration accumulation, future reuse extension/conflicts, instruction
and frame budgets and exact checked-error precedence. Nested sequence folds
define expansion order and absorb exhaustion/errors; their inputs are the
composition metadata, not a supplied successful trace.

`part2_render_normalized_frame` composes actual selection, indexed layer-result
resolution and the complete renderer. A supplied outcome bank contains layer
references paired with optional normalized results. Lookup consumes the
first remaining matching result, allowing arbitrary ordering, repeated keys,
unrelated/error entries and empty slots. There is no canonical-bank or
trace-validity precondition. Missing referenced results reject with
`InvalidBoxContents`. Repeated references consume successive supplied
outcomes, preserving per-placement semantics without a cache assumption.
All selected normalized results are gathered before any placement runs;
therefore their first failure precedes any pixel/work/byte failure in earlier
successful supplied layers. The complete final image model is then the
ordered supplied-layer renderer above.

These are whole actual-function contracts, not only helper properties.
Independent tests exercise multilayer/multiframe rational buffers, all
four-frame persistence masks, finite/indefinite selection, reference-bank
permutations, distinct repeated outcomes, full timeline expansion/reuse/
timing and typed failures. Parsing, compressed-data correctness,
normalization, registration, opacity and chroma-key policies remain separate
packages. Integration and owner acceptance are not implied by local proof
success.

The actual raster and first-failure definitions remain here. In particular,
`part2_composition_budgeted_prefix` determines execution order and error/state
propagation and must be audited as part of the layer denotation. Its solver
opacity does not remove that obligation; the body and checked base/step/
absorption proofs remain available.

Prefix-membership witnesses used only to establish an additional safety
property live in [proofs/internal_specs.rs](../proofs/internal_specs.rs).
Compatibility re-exports in `mod.rs` do not make those induction details part
of the normative reading path. Representation views and mathematical/
production refinement lemmas remain in their existing proof modules.

Resource policies are audited separately from coding semantics: each stored
pixel charges one unit per active output color plus one alpha unit. Stores
precede charging; overflow preserves the stores and old counter, and a work
limit error preserves stores and the incremented counter. These are selected
bounded-decoder behaviors, not newly asserted normative JPEG 2000 equations.
The complete native tile-component geometry relations
`part2_tile_component_bounds`, `part2_registered_component_ceil` and
`part2_registered_decode_ceil` describe actual raw tile/component/registration
inputs and exact typed Results. Tile geometry precedes descriptor admission;
the typed-layout decoder's separate zero-divisor error is preserved while both consumers
execute the same registered-ceiling body. No admitted geometry, normalized
descriptor or supplied scalar outcome is a premise. Complete packet planning
and the F2/F4/F8 file/decoder joins remain separate.
The actual resolution-style relations `part2_resolution_downsampling`,
`part2_resolution_scale_step`, `part2_resolution_scale_prefix` and
`part2_precinct_exponents` retain ordered raw descriptor lookup and checked
scaling, including early overflow versus physical-array exhaustion. Prefix
error absorption is proved in production support. Raw precinct pairs are not
normalized to their downstream limit, and unused fields stay unvalidated.
No supplied lookup/scaling result or normalized style is a premise.
`part2_resolution_geometry` derives the full actual public/private resolution
geometry Result from raw size/component/style/tile metadata. Component bounds,
real downsampling, checked extents and ordered code-block/precinct grids are
modeled without successful intermediate results as premises. Native
whole-image registration omission and the reported nonzero-resolution
subband value3 are preserved explicitly, not silently normalized away.
Public-boundary and exact native-consumer recipes bind all four contracts.
`part2_packet_grid_from_components` connects raw owners and limits to the
complete actual grid constructor through real resolution admission, geometry,
subband deltas and ordered precinct/code-block accounting. Suffix runs retain
initial-versus-late error policy, zero padding and discarded finest geometry.
They are mathematical folds over actual inputs, not supplied grid/count/result
banks. A production transition lemma links the original nested loops, and
exact raw-owner/limit recipes bind both native producers.
The complete raw subband admission models `part2_quantization_lookup`,
`part2_quantization_step_at_index`, `part2_quantization_for_subband` and
`part2_make_subband_geometry` retain actual logical/physical lookup, derived
step0/saturating exponent behavior and original bitplane/extent error order.
Public orientation admission is not silently imposed on the internal raw
geometry helper. Every result field derives from original metadata; no
normalized depth/step/bounds or successful lookup/scaling result is a premise.
`part2_component_subbands` derives the complete actual ordered subband vector
from original image/style/quantization/component/tile/ROI inputs. Raw truncated
counts, resolution steps, phases, anisotropic order, growing checked indices,
final count checks and first errors remain explicit. The public boundary and
three native consumer contracts bind the sole executable traversal; no
prepared band vector, normalized geometry/count or supplied lookup result is
a premise. Full tile-plan and F2/F4/F8 composition remain separate.
`part2_tier1_initial_decoder` describes actual raw decoder construction,
including the real empty plane and every initial legacy/HT field. Native
style/HT policy setter models preserve all unrelated raw state and retain
the owner on invalid bounds. Actual planner/public facade calls share the
sole constructor; no supplied initialized decoder/plane, normalized style or
successful allocation is a premise.
`part2_planned_codeblock_geometry` and `part2_tier1_configured_decoder` describe
the actual raw inner tile-loop producers: ordered checked nominal coordinates,
clipping, dimension narrowing and real initialized/policy-configured decoder
state. Zero dimensions are not normalized away, and no valid grid/decoder
outcome or successful allocation/budget is assumed. Full tile-plan vector
composition and F2/F4/F8 remain separate.
The actual precinct constructor models `part2_precinct_contexts`,
`part2_precinct_execution`, `part2_precinct_initialization_run` and
`part2_precinct_from_executions` derive every owned field from raw execution
vectors/style/limits and real state/tag-tree producers. Native future-buffer
frames and moved decoder contents are proved, not supplied as initial-result
banks. Empty/raw coordinate policy and first/late budget/shape errors remain
explicit. Complete tile-plan and F2/F4/F8 joins remain separate.
`part2_component_plan_metadata` composes actual raw owner/selection metadata
through style, quantization, route, full geometry, position, ROI and real
subband production. Getter models preserve logical versus physical owner
admission. Native output/state views bind all fields without prepared metadata
or supplied intermediate success/result premises; full tile-plan and
F2/F4/F8 composition remain separate.
`part2_planned_codeblocks` and its cell/column/row suffix relations derive
the actual decoder/placement buffers, flattened index and selected-only
global code-block accounting from raw lattice, clipping, shape, subband,
style, policy, location, owned prefix, count, selection and limits. Actual
configured initialization is composed directly, not supplied as a result.
Native views bind every owned decoder/placement field and existing-prefix
frame; all intermediate bounds and traversal frames are proved internally.
`part2_planned_subband_lattice` derives optional intersection/lattice/shape
from raw band/block/subband fields. `part2_planned_subband_execution` composes
that actual producer with real configured decoder vectors, packet-row metadata
and complete owned placement/index/accounting state. Empty-intersection
laziness and preceding arithmetic, divisor, limit and initializer error order
remain explicit; no prepared lattice, decoder/result bank or successful
resource premise is supplied.
`part2_planned_precinct` derives complete private packet state and owned
placement/accounting output from raw band/block geometry, subband source and
range, style/policy/location/selection/limits. Its source-index and suffix
relations produce actual optional subband executions and decoder vectors,
then invoke the actual packet-initialization model. No prepared execution or
decoder bank, validated range or successful resource premise is supplied.
Native owned-state invariants prove all intermediate indexing and append
frames; complete tile-plan and F2/F4/F8 joins remain separate.
`part2_resolution_plan_metadata` derives the actual complete resolution-loop
metadata from raw image/style/component/selection and unnormalized component
origin. Its internal finish stage receives geometry/ranges/counts derived
inside that relation, never supplied successful results or premises.
`part2_planned_precinct_origin` retains raw checked first-grid/precinct/band
arithmetic. Native views and exact recipes bind every metadata field,
including zero-band lazy narrowing and later independent validation.
`part2_planned_component` derives complete component and existing/new
precinct vectors from actual raw owner metadata, resolution preparation and
real precinct producers. `part2_progression_tile_plan` composes actual first
tile bounds, selected grid and all actual component results into the complete
private tile plan. Non-mutual suffix folds retain all owned state, prefixes,
indices and budget/error order; no successful intermediate plan, metadata,
geometry or decoder result bank is supplied as a premise.
The public component-owner entry binds the same relation and original defaults;
packet/output/file/F2/F4/final F8 and uniform-owner facade joins remain separate.
`part2_decode_planned_tile_components` composes actual byte-executing F5
progression semantics with the real F6/F7 tile reconstruction. Proved native
decoder/precinct/vector observations justify `part2_precinct_decoder_planes`;
planes and prepared outcomes are not supplied as successful results.
The complete owned output includes every component/sample field and MCT work,
preserving raw existing-prefix frames and full/selected error order.
Real layout callers use actual produced plans, unchanged metadata/global
accounting and this sole join; whole raw-layout/file/F2/F4/F8 closure remains
separate.
`part2_planned_tile_accounting` composes actual grid admission/counts and
ordered global packet/precinct/codeblock limits from raw complete plan state,
optional resolution counts, arbitrary prior counters and actual limits.
`part2_selected_component_blocks` and `part2_account_plan_blocks` retain raw
placement/subband lookups, per-component full versus final-only selected
limit checks and empty-component laziness. All intermediate bounds and
counter relations are proved, not successful count or normalized-plan premises.
`part2_tile_decode_metadata` derives actual first/MCT/kernel/style metadata
from raw tile parts, component count and optional discard mode.
Exact MCT identity relations preserve every encoded owner field, not normalized
numeric equality; style suffixes preserve the original builtin-only decoder
wavelet agreement, maximum-isotropic physical prefix and checked reduction
policy. Internal derived mode/prefix/sequence witnesses establish the complete
postconditions without supplied successful equality, kernel or metadata
outcomes. Actual full/selected callers execute the sole native producers.
`part2_capability_value` derives physical CAP lookup from actual raw mask
and word observations through a terminating mask/index suffix. Exact part15
and profile policy relations retain invalid-mode, missing/ragged/default and
unused-owner behavior without normalized metadata or supplied result premises.
Native field views and eight exact recipes bind every actual layout policy
getter; the low-five-bit magnitude bound is proved locally, not assumed.
`part2_decode_tile_parts_at` derives complete per-tile prepared/sample output,
global packet/precinct/codeblock counters and MCT work from actual raw tile
parts/image/profile/mode/limits and owned prior accumulation. It composes the
actual metadata, policy, raw-owner planning, accounting and byte/reconstruction
relations in source order; no successful intermediate plan/decoded/sample bank
is supplied. Actual full/selected callers execute the sole native body.
Collection/clone, whole layout/parser/file/F2/F4/F8 joins remain separate.
Complete owned metadata observations retain every raw nonlinear/Part2/kernel/
MCT/quantization/progression/header/flag/data field for actual Clone refinement.
`part2_tile_part_copy` is logical data identity, not opaque allocation identity;
`part2_collect_tile_parts` derives the ordered source-filtered observations
through the actual clone-before-filter suffix. Native bodies preserve prior
field and allocation order, with no assumed clone or successful outcome bank.
Complete source-derived `Part2OwnedTilePart` observations are the mathematical
tile-codec operands. Legacy native-payload entries are thin projection wrappers
over the same owned-data algorithm; they do not introduce normalized input,
copy/result witnesses or a second decoder. Actual cloned inputs with equal
complete data have proved equal metadata, byte-execution and raw-tile outcomes,
without equating opaque heap allocations. Native API bindings and actual
Rust decoding behavior remain unchanged.
`part2_decode_layout` and `part2_decode_layout_selected` compose actual
Part2/count/selection admission, source-owned tile collection, real raw
per-tile decoding from empty accumulation and full/selected assembly.
Complete fixed image/sample outcomes and first errors contain no supplied
decoded/planning/copy witness banks or normalized-layout premises. The
native loops establish all count/work/source/selection frames internally.
Raw parser/typed/file/F2/F4/final F8 joins remain separate.

## Component entry points and boundaries

| Component | Actual source → model | Current boundary to keep in view |
|---|---|---|
| Bytes / containers | [codestream.rs](../src/codestream.rs), [jp2.rs](../src/jp2.rs), [jpx.rs](../src/jpx.rs), [jpip.rs](../src/jpip.rs) → [mod.rs](mod.rs): `part1_codestream_read_segment`, `part9_*`, `part2_*` | Raw reader, metadata, container and selection contracts have distinct inputs; a local marker theorem is not the whole public decoder. See [container composition](../PROOFS.md#complete-native-container-selection-and-typed-output-composition). |
| Packet / entropy | [packet.rs](../src/packet.rs), [mq.rs](../src/mq.rs), [tier1.rs](../src/tier1.rs) → [packet_input.rs](packet_input.rs), [header.rs](header.rs), [tag_tree.rs](tag_tree.rs), [packet.rs](packet.rs), [mq.rs](mq.rs), [legacy.rs](legacy.rs), [mod.rs](mod.rs): `part15_*` | Reader, traversal, retained-contribution and coefficient-state relations must be composed explicitly. See [mixed dispatch](../PROOFS.md#complete-unconditional-mixed-contribution-body-and-tier-1-dispatch). |
| Coefficients / arithmetic | [magnitude.rs](../src/magnitude.rs), [tier1.rs](../src/tier1.rs), [refinement.rs](../src/refinement.rs) → [mod.rs](mod.rs): `part1_magnitude_value`, `ht_cleanup_plane` | Full 384-bit arithmetic support is not HT byte meaning; supplied metadata/bytes and raw coefficient frames remain explicit. See [magnitude interface](AUDIT_REFERENCE.md#full-native-magnitude-interface). |
| Transforms | [transform.rs](../src/transform.rs), [reconstruction.rs](../src/decode/reconstruction.rs) → [mod.rs](mod.rs): `part1_inverse_quantization`, `part1_inverse_level`, `part1_apply_component_transform` | Stage contracts distinguish supplied coefficients, prepared components and real owner buffers. Deterministic fixed-point behavior alone establishes no normative tolerance. See [reconstruction](README.md#reconstruction-reading-path). |
| Channels / color | [output.rs](../src/decode/output.rs), [jp2.rs](../src/jp2.rs), [color.rs](../src/color.rs) → [mod.rs](mod.rs): `part2_palette_component`, `color_convert_jp2`, `color_convert_selected` | Palette/CDEF routing, registration, conversion and crop have separate admissions. Supported enumerations and ICC rejection are explicit. See [semantic detail](AUDIT_REFERENCE.md#semantic-definitions-versus-internal-proof-support). |
| Layers / frames | [jpx.rs](../src/jpx.rs) → [mod.rs](mod.rs): `part2_layer_input`, `part2_build_timeline`, `part2_render_normalized_frame` | Normalized 16-bit source-over and floor-scaled sampling are selected policy. Timeline/frame results are input-relative, not proofs of compressed decoding or container normalization. See [composition vocabulary](AUDIT_REFERENCE.md#normalized-source-over-vocabulary). |

## Worked example 1: full-width magnitude addition

**Code → model.** Open `Magnitude::checked_add` in
[src/magnitude.rs](../src/magnitude.rs). It adds six little-endian `u64` limbs
with a carry. Its closed `magnitude_value` projection is defined by
`part1_magnitude_value` in [mod.rs](mod.rs): the natural value of all 384 bits.
`magnitude_addition` is natural addition; `part1_magnitude_capacity()` is `2^384`.
No normalized-coefficient or HT-success premise is required.

**Contract.** The adjacent `verus_spec` binds both operands to that full-value
view. If their sum is below capacity, the result is `Ok` with exactly that sum
and the raw/value representation relation. Otherwise the result is exactly
`MalformedInput { offset: 0, kind: ArithmeticOverflow }`, expressed through
`part1_transform_error(true)`. This is a finite-capacity arithmetic theorem,
not a theorem that compressed bytes denote a particular coefficient.

**Proof / test.** Follow the loop's prefix-sum/carry invariant and
`production_magnitude_add_prefix_step`, `production_magnitude_add_limb`, and
`production_magnitude_prefix_update` in
[proofs/production_impl/mod.rs](../proofs/production_impl/mod.rs).
`exact_full_capacity_addition_matches_bit_carry_reference` in
[src/magnitude.rs](../src/magnitude.rs) independently compares bit-array addition,
including complete carry propagation and exact overflow errors. The
[arithmetic boundary](../PROOFS.md#full-native-magnitude-arithmetic) explains
how this supports reconstruction without proving HT byte semantics or a
completed ITU-clause audit.

## Worked example 2: PLM packet-length admission

**Code → model.** Open `Parser::parse_plm` and its actual callee
`Parser::validate_packet_lengths` in
[packet_headers.rs](../src/codestream/packet_headers.rs).
Their models in [mod.rs](mod.rs) are `part1_parse_plm`,
`part1_plm_groups_from`, `part1_validate_packet_lengths`, and
`part1_packet_length_admission_from`. The raw variable-length decoder is modeled
by `part1_packet_length_decode` in [packet_input.rs](packet_input.rs).
Group lengths and borrowed byte slices derive from the real segment payload,
not supplied decoded lengths or a bank of decoder results.

**Contract.** Each adjacent `verus_spec` equates the actual result and final
state with the model from the initial raw state. Admission binds the complete
parser view; PLM also binds the next index and all group views, including
arbitrary preexisting groups. Read the ordering, not just the successful count:

- Minimum payload length and index checks precede the PLM index increment.
  A successful index admission, including 255 → 256, survives later failure.
- Packet-header-byte addition commits before its cap check. Genuine work
  charging precedes variable-length traversal; malformed varints retain these
  charges but do not commit a packet count.
- Completed traversal commits the global packet count before its cap check.
  A successful group is appended before the tile-part cap check, so that
  failure retains the appended group.
- Work errors use the parser position; byte/count overflow and malformed
  varints use the marker offset. Empty encoded input still checks counters.

The relations preserve typed first failures, partial commits and untouched
parser/group fields; they do not prove PLT/final metadata or the outer
parser/decoder joins.

**Proof / test.** Follow `parser_view`, `segment_view`,
`packet_length_groups_view`, the source-derived traversal invariants, and
`decode_packet_length` / `Parser::charge_work` in the same source file.
Independent wide-arithmetic tests in the
[parser test module](../src/codestream/tests.rs) include
`actual_packet_length_admission_preserves_byte_work_packet_overflow_and_limit_commits`
and `actual_plm_groups_preserve_charge_errors_append_caps_and_real_segment_reader_join`.
The [PLM boundary](../PROOFS.md#actual-packet-length-admission-and-plm-group-production)
and inventory enumerate the remaining evidence. This reading example is not a
completed normative clause walkthrough or official conformance evidence.
