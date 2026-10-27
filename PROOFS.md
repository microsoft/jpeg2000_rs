# Verus proofs

<!-- Temporary documentation-only hold-routing fixture. Never merge. -->

## Reading this document

The sections below describe individual contract boundaries, including narrower
relations that are composed by later sections. They are not a chronological
progress board, a release attestation, or a claim that the entire public
decoder is proved from raw bytes through frame output. In particular, a
complete relation for parsed layouts or supplied normalized samples does not
prove the parsing or normalization that produced those inputs.

Use the maintained [technical reference inventory](validation/normative-coverage.json)
and [auditor reading path](specs/README.md) to locate current executable
contracts and models. Exact run counts and source/tool hashes belong in fresh
CI artifacts, not committed result snapshots. Independent model-to-standard
review and official conformance testing remain separate.

## Single executable implementation

Cargo and Verus use the exact [src/lib.rs](src/lib.rs) crate root. Production
algorithms live in [src/](src/); a second proof-only decoder implementation is
not maintained.

Verus-only attributes and modules are enabled with `verus_keep_ghost`:

- [src/refinement.rs](src/refinement.rs) contains executable helpers with
  functional contracts.
- [specs/](specs/) contains mathematical models.
- [proofs/shared/](proofs/shared/) contains representation views.
- [proofs/spec_properties/](proofs/spec_properties/) contains model lemmas.
- [proofs/production_impl/](proofs/production_impl/) contains refinement lemmas.
- [proofs/internal_specs.rs](proofs/internal_specs.rs) contains auxiliary
  prefix-membership witnesses, not algorithm denotations.

Start semantic review with the [specification audit guide](specs/README.md),
which distinguishes selected reference editions, normalization policies and
internal proof support. Essential raster/first-failure semantics remain on
that reading path.

Ordinary Rust builds erase ghost code and retain Rust's borrow checking.
Source and proof changes must be validated together.

## Temporary model-review hold

The [model-review hold](.github/workflows/model-review-hold.yml) is a
conservative engineering freeze while document-use, independent-review and
trusted-adjudicator decisions are pending. It is not approval of any model's
correspondence with an ITU edition.

The [controller](validation/check-model-review-hold.py) holds changes to any
Rust source, all files under `src/`, `.cargo/` and `.github/`, non-Markdown
files under `specs/`, `proofs/` and `validation/`, and Cargo/toolchain manifests
and locks. This deliberately includes implementation-only edits, representation
changes, tests and the controller itself: it does not try to infer semantic
equivalence from a diff. Markdown audit-guide changes remain possible; their
claims still need human review.

The workflow uses `pull_request_target`, checks out the event's base commit,
and runs only its controller. It fetches but never checks out or executes the
proposed code. It assesses committed changes from the unique merge base,
including deletions and renames. A policy edit in the same proposal cannot
grant itself an exception. Missing history or ambiguous merge bases fail.

This initial hold has **no approved-amendment override**. Replacing it with
a separately reviewed amendment process requires actual trusted reviewer
identities, source-bound evidence and owner authorization; a candidate's own
`approved` flag is not an approval. It does not complete that governance work.
An owner-approved transition must arrange replacement of the hold rather
than treating a held change as approved.

The check becomes available only after the workflow is merged into the target
branch. Its presence does not configure branch protection or prevent direct
pushes, administrative bypasses or changes to repository settings. Required
checks/reviews and controller ownership need owner configuration and live
demonstration before enforcement can be claimed. Existing Verus, runtime,
numerical, resource and evidence gates remain unchanged.

Run the controller regressions with
`python3 -m unittest validation.tests.test_model_review_hold -v`.

## Actual packet-length admission and PLM group production

Actual packet-length admission binds its full parser state and result to the
raw encoded bytes and marker offset. Header-byte addition commits before its
limit check, and genuine work charging precedes the actual variable-length
decoder. Malformed varints retain those charges but do not commit packet
counts. Completed traversal commits the global packet count before its limit
check. Work errors use the parser position; byte/count overflow and malformed
varints use the marker offset. Empty input still performs all counter checks.

Actual PLM parsing derives every group length and borrowed source slice from
the payload. Minimum length and index checks precede incrementing the index,
including 255 to 256. That increment and genuine admission partial commits
survive later errors. Successful groups append before the tile-part cap, so
that error retains the appended group. Arbitrary preexisting groups retain
their order, source variants, counters and encoded-byte metadata.

Both sole executable bodies have exact total contracts, full initial-state
and recursive-fold loop links, and checked mathematical termination. No
admitted varints, normalized groups/counters, result banks, new trust,
caps, pins, budgets or termination bypass are introduced. Independent
wide-arithmetic references cover 786,432 short-varint contexts, 12,000
charge/overflow/limit contexts, 156,672 PLM index/truncation/frame contexts,
262,144 raw length words and 1,080 PLM partial-commit contexts. A real segment
reader joins three borrowed groups, including an empty group. These tests
are not official conformance evidence. PLT/final metadata and outer
parser/F2/F4/F8 joins remain separate.

## Actual packed-header fragment and PPM-frame byte production

Actual packed-fragment admission binds the complete parser state and every
external next-index, fragment-count and accumulated-byte field on all results.
Marker/empty/order checks precede the index increment; that increment survives
fragment-count overflow. Both increments survive later byte/work errors.
Packet-header bytes commit before the genuine work charge, so work overflow
or limits retain that byte-counter update without appending payload bytes.
Work errors retain the parser-position offset, distinct from segment errors.

Actual PPM framing derives every big-endian source length, frame start and
checked end position. Zero fragments bypass all source validation and yield
no frames; nonzero fragments retain empty input, zero-length frames,
short-header versus oversized-body offsets, and the post-push tile-part cap.
Both sole executable bodies have exact contracts without admitted frames,
prepared payloads, normalized counters, result banks, new trust/caps/pins/
budgets or termination bypass. PLT and final metadata/parser/F2/F4/F8
joins remain separate.

Independent wide-arithmetic and byte references cover 147,456 index/marker/
counter contexts, 24 empty payloads, 18,000 charge/overflow/limit contexts,
1,179,648 PPM length/count/cap contexts and 435 compound truncations.
A real two-segment PPM reader joins a split length word to three genuine
frames and checks all counters, data, input identity and work. These
regressions are not official conformance evidence.

## Complete native MCT graph resolution

The actual resolver derives its full optional graph from every raw array,
record and order field, consuming the proved first-record and unique ID/kind
array producers. An empty order retains the native `None` bypass even with
unused arrays or records. Nonempty raw orders may repeat IDs, first duplicate
records win, and raw empty records produce empty stages without a validated
registry premise.

The sole collection body checks nonzero/equal dimensions, resolves offsets
before matrices with zero-index bypasses, executes actual checked element
arithmetic, then rejects bad dimensions or floating reversible arrays. The
count model preserves overflow of the intermediate product before halving,
reversible row increment and final subtraction, including arbitrary native
usize boundaries. The raw Offset kind retains its original non-Dependency
collection-kind mapping rather than being normalized out.

Array clones retain index, kind, numeric format, fraction bits and all values.
Wavelet fields, reversibility, arbitrary component lists, stage IDs and
encounter order are all bound. Canonical-root and suffix-fold invariants
cover every early error in the actual collection/stage/graph traversal.
Four exact contracts add no prepared graph, admitted dimension, supplied
decoder outcome, new trust/cap/pin/budget or termination bypass. Actual
parser-to-parameter and outer file/layer/F2/F4/F8 joins remain separate.

Independent u128 arithmetic and iterator/reference construction exercise
native word boundaries, 165,888 array-collection contexts, 648 wavelet
contexts, 9,216 stages and 73,728 complete parameter/order contexts. Full raw
outputs and first-error behavior are compared, including duplicate IDs,
unused data, missing references and reversible/irreversible field regimes.
These engineering regressions are not official conformance evidence.

## Native MCT registry admission, replacement and reference production

Actual array and MCC-record admission checks only the last element against
the earlier prefix. Earlier duplicates remain admissible when the last ID is
unique; no whole-registry uniqueness premise is introduced. Sole first-index
lookups serve both this check and replace-or-append. Replacement uses the ID
alone, preserves later duplicates and order, and binds every raw array field
and every record/collection/reference field.

Actual borrowed-array resolution requires exactly one matching ID and kind.
Other kinds with the same ID are ignored; zero or multiple matching arrays
retain `InvalidTransform` at offset zero. Numerical format, fraction bits,
values and dimensions remain unvalidated by this lookup. The canonical root
and traversal invariant are explicitly linked, including early duplicate
failure, rather than relying on a locally prepared lookup result.

Seven exact contracts bind both read-only results and the full old/final
unit-return mutation frames, without changing the implicit unit signatures.
No normalized registries, unique-index assumptions, result banks, new trust,
caps, pins, budgets or termination bypass are introduced. Actual transform
graph dimensions/resolution and the outer parser/F2/F4/F8 joins remain separate.

Independent iterator/reference updates check 55,296 array and 18,432 raw
record contexts, including empty/zero/duplicate IDs and every raw array
kind/format/fraction regime. They compare 442,368 full array replacements
and 147,456 full record replacements, and 73,728 exact ID/kind references
including borrowed input identity. These are maintained regressions, not
official conformance evidence.

## Complete native MCT fragment state and numeric-array production

Actual MCT fragment consumption binds every pending descriptor, next/final
index, original offset and data byte, plus every completed ID, on success
and failure. The sole staging body derives its square-times-eight byte bound
from the actual component limit. Lookup selects the first matching low-byte
array ID; continuations then require the full descriptor and exact next
index. Initial fragments alone reject previously completed IDs.

Continuation append precedes byte-cap and next-index overflow errors, and
those writes remain observable. Exact completion uses native swap removal,
reconstructs the actual six-byte header and source data, and composes the
proved numeric-array parser rather than accepting an array result. Removal
precedes numeric/header errors; successful continuation may append a duplicate
completed ID. The stored first-fragment offset governs parser errors.

Four exact contracts bind the sole staging, lookup, shared membership and
consuming bodies, including both mutable frames. Source-derived bounds prove
every read, cast, multiplication and traversal without normalized prior
fragments, supplied payloads/results, new trust, caps, pins, budgets or a
termination bypass. Transform graph replacement/resolution and outer
file/layer/F2/F4/final F8 joins remain separate.

Independent endian/u128/staging and existing numeric references cover all
65,536 descriptors in 262,144 state contexts, 105 short headers, 1,278 numeric
split/reassembly contexts, 1,280 first-match lookups, 270 byte/overflow
boundaries, all 65,536 component-limit words and 196,608 final-index contexts.
A real reader joins split binary64 success and later binary32 nonfinite
failure, checking pending removal, original error offset and completed IDs.
These maintained regressions are not official conformance.

## Complete native raw MCT numeric arrays

Actual MCT parsing binds every array index/kind/format/fraction/value field
from raw source bytes and actual limits. Minimum header, Z/Y/reserved/index/
kind/alignment and actual component-square element limits precede numerical
conversion. The sole factored element body consumes real signed/packed word
and deterministic IEEE32/64 producers for all four original formats.

The existing proved ATK binary-format/Q32 mathematical definitions are reused
through exact unit-error projection, retaining the original stricter MCT
exponent guard. Signed zeros, nonfinite rejection, ties-to-even, large-right
underflow and signed/unsigned overflow branches preserve native outcomes.
Explicit cross-width bit facts, safe exponent casts and boolean increments
expose source values rather than assuming normalized IEEE inputs or supplying
converted-element banks. Every read/advance/decrease bound follows from real
header/count geometry.

The mathematical value fold exposes each positive format stride and rejects
an incomplete trailing element before recurring. Its remaining-byte measure
therefore stays nonnegative and strictly decreases, including for arbitrary
unaligned model inputs. The executable element checks and decoder are
unchanged; a codestream-only proof does not check this specification's
termination obligation, so complete-root verification remains mandatory.

Seven exact contracts bind actual numerical and byte producers to the full
array Result. No new trust, caps, pins, solver budgets or termination bypass
is introduced. Actual MCT fragment state, graph and outer file/layer/F2/F4/
final F8 joins remain separate.

Independent division/remainder/endian references compare 816 generic binary
frontiers, 5,060 ties-to-even cases, 3,584 binary32 and 28,672 binary64 field
contexts, and 262,144 paired full-word patterns for both formats. Packed64/
signed16 checks cover all 65,536 word values plus 2,048 byte mutations.
Complete arrays cover 786,432 descriptor contexts, 3,456 mixed-format/value
contexts, 576 count/alignment/limit boundaries and 3,456 element bounds.
A real reader joins accepted binary32/binary64 arrays and later nonfinite
rejection. Generic right shifts of 128 or more retain native zero-underflow
policy; these maintained regressions are not official conformance.

## Complete native MCC fragment state and record production

Actual MCC fragment consumption binds the optional genuine record Result,
all pending fields/data/order and completed IDs for arbitrary raw prior state.
The sole staging body composes real first-match and completed-membership scans.
Initial fragments reject prior active/completed IDs before byte limits;
continuations retain their original completed-ID permissiveness. Source-derived
component byte limits and append-before-cap/next-overflow commits remain exact.

Completion uses the existing exact next-equals-final-plus-one producer, not
an assumed valid sequence. Actual swap-remove ordering is framed. Pending
removal happens before cap/record errors, and the real seven-byte reconstruction
uses stored metadata/data and original offset before the actual proved MCC
parser runs. Completed IDs append only after real record success.

Four exact contracts expose these producers and every mutable frame without
normalized pending/completed consistency, prepared reconstruction or decoded
record banks. Explicit concatenation/update equalities bind nested data writes;
standard vector removal facts retain native order and allocation policy.
No new trust, caps, pins, solver budgets or termination bypass is introduced.
Numeric MCT/other fragment/graph and outer file/layer/F2/F4/final F8 joins
remain separate.

Independent wide-limit/state-transition references compare 1,179,648 fragment
header contexts, 10,080 initial-admission contexts and 135,000 continuation/
first-match/partial-failure contexts. Thirty-three real record split sequences,
1,280 arbitrary lookup/membership cases and 120 byte/next-boundary cases
check raw prior state, swap ordering, original error offsets and continuation
completed-ID permissiveness. A real two-marker reader reconstructs and parses
the genuine record. These are maintained regressions, not official conformance.

## Complete native raw MCC collection records

Actual MCC parsing now binds the complete record/index and every collection
field from raw bytes, component count and actual limits. Minimum header,
Z/Y/index/count and TransformElements checks precede the sole factored
collection body. Real routing-list producers supply all references; original
kind/list/descriptor/wavelet/terminal order remains explicit.

Dependency input/output lists must match in order, while decorrelation may
permute. Raw reversible/array/offset indices, wavelet type, levels 0..32 and
the complete signed-32 component offset are retained without graph or array
existence premises. Actual signed conversion provides its safe i32 bound;
derived-safe narrowing replaces an impossible conversion error. Existing
proved list equality and explicit bit-mask facts expose actual source values.

Terminal length admission precedes the actual parallel check. Its sole
overlap body is moved and proved: any input/output intersection across
collections fails, but within-collection overlap and unrelated raw fields are
not newly validated. Explicit conflict witnesses bind both failure and success.
Five exact contracts and private physical views compose without normalized
collections, prepared descriptors, new trust, caps, pins or solver budgets.
Actual numeric arrays, fragment state/graph and outer file/layer/F2/F4/final F8
joins remain separate.

Independent byte-arithmetic/endian/set references compare 40,960 kind/start
contexts, 27,648 descriptor mutations, 35,280 routing/length contexts,
262,144 count-limit contexts, 248,832 raw header contexts and 7,884 complete
record/terminal/parallel contexts. Signed conversion and overlap scans each
cover 262,144 cases; 2,592 raw parallel pairs and 1,152 wavelet-offset cases
cover otherwise-invalid metadata and exact branch boundaries. A real reader
joins disjoint array/wavelet records and later cross-route conflict failure.
These are maintained regressions, not official conformance.

## Complete native raw transform-routing lists

Actual MCO stage-order and MCC component-list syntax now bind full Results
from raw bytes and offsets. MCO preserves exact count before duplicate/
nonzero checks, encounter order and the valid zero-stage empty order; stage
existence belongs to later graph resolution, not a new syntax condition.

MCC derives one/two-byte references from the header's high bit independently
of Csiz, and lower-fifteen-bit counts from the actual word. Header truncation
leaves the external cursor untouched; invalid count or remaining length
retains its two-byte advance. Valid references advance in order, while an
out-of-range or duplicate current value fails at that value's start.
Component zero remains valid. The sole existing membership scan is moved out
of its nested declaration and proved, without duplicating runtime bodies.

Three exact contracts bind these actual producers and every cursor failure
frame. Existing byte/word outcome observations, explicit equivalent range
guards and derived-safe count arithmetic require no normalized route/order,
reference banks, graph-success premises, trust, cap, pin or solver changes.
Numeric/collection parsing, fragment state and graph resolution, and outer
file/layer/F2/F4/final F8 joins remain separate.

Independent set/endian/wide-cursor references compare 3,584 MCO count
frontiers, 131,072 stage-pair contexts and 11,264 byte mutations. MCC checks
cover 2,400 cursor frontiers, 1,310,720 encoded-header contexts, 786,432
reference-word contexts and 2,880 complete-list/order/length cases.
The actual membership scan is checked in 327,680 contexts. A real reader
joins MCO with narrow and wide actual MCC callers, preserving route order
and the later duplicate-MCO error offset. These are maintained native
regressions, not official conformance.

## Complete native semantic progression admission

Actual progression admission binds its complete Result from raw records,
layers, the actual component-style owner and actual work cap. Empty input
bypasses all style/budget checks. Otherwise real style lookup, depth increment
and coordinate arithmetic precede the calculated records-times-active work
comparison, then record bounds, fresh contribution and final coverage.
Existing parser work counters are not charged by this read-only validation.

The sole factored resolution/layer/component loops bind arbitrary scratch
bitmaps and exact partial mutations on errors, without admitted rows, style/
bitmap validity, successful coverage or prepared outcomes. Every record must
add a previously-unowned active coordinate: partial overlaps remain legal,
entirely redundant records fail, and the final union must cover every active
coordinate. Heterogeneous depths, raw count/depth errors, zero layers and
unused style fields retain native order and behavior.

The real completion scan, existing window predicate and range denotation
compose through six exact contracts. Explicit initial and already-owned
sequence equalities expose actual bitmap effects rather than adding trust.
No new caps, pins, solver budgets or termination opt-outs are introduced.
Independent wide-arithmetic and coordinate-set references compare 770 raw
shape/empty-bypass cases, 54,000 resolution scans, 57,600 layer scans, 12,960
complete record/partial-bitmap cases and 8,191 completion bitmaps. Another
60,288 complete-admission contexts check empty/single/pair windows against
calculated-work caps at zero, cost-minus-one, exact cost and cost-plus-one.
Explicit partial-overlap acceptance and redundant-record rejection distinguish
the native fresh-contribution policy from an incorrect disjointness rule.
All parser fields remain unchanged; these are maintained regressions, not
official conformance.
Remaining fragmented transform/packet/layout/file/layer/F2/F4/final F8 joins
stay separate.

## Complete native raw POC progression records

Actual POC syntax parsing binds the full Result and every physical record
field from raw bytes, component count and segment offset. The real byte/
component readers retain width-one versus every-other-width two-byte behavior,
overflow/range ordering and segment rather than current-cursor offsets.

Source-derived alignment and count geometry establish every seven/nine-byte
read, advance and termination bound at component threshold 257. Empty and
alignment errors precede progression-byte admission; order codes 0..4 retain
the existing shared mathematical mapping. Encoded component end zero becomes
256 only for Csiz 256. Other raw layer/resolution/component fields, including
otherwise-invalid ranges, are retained without normalization.

Three curated exact contracts bind the actual readers and complete record
production without prepared records, valid-range/coverage premises, new trust,
caps, pins or solver-budget changes. The real downstream range, coverage and
duplicate validation is explicitly not proved by this syntax milestone.
The separate semantic-admission section above covers that actual consumer.
Independent chunk/endian references compare 7,200 helper frontiers, 524,288
word/fallback contexts, 131,072 component-count contexts, 786,432 raw record
word contexts, 179,712 full-byte/alignment mutations and 600 length/error
frontiers. A real three-marker reader join retains syntactically accepted
invalid ranges and rejects the later bad order byte at its segment offset.
Complete unchanged parser fields and arbitrary helper widths are checked;
these are maintained native regressions, not official conformance.
Remaining metadata/layout/file/layer/F2/F4/final F8 joins stay separate.

## Complete native raw ATK kernels

Actual ATK parsing binds the complete raw kernel Result, every coefficient
byte/width and lifting-step field, and all parser/eight extension fields.
Real metadata/work charge precedes the minimum-seven-byte header, descriptor
index/type/reserved admission, optional scaling and raw step traversal.
Original offset/exponent/residue/count/coefficient/terminal ordering remains
explicit, including zero-count and trailing-byte errors. First-index registry
replacement preserves later duplicates and unrelated arbitrary raw owners.

The sole actual lifting-step and payload bodies compose real coefficient
reads. The reader binds all sixteen physical slots with exact right alignment
and integer-only sign extension, including arbitrary raw width/type inputs.
Width errors precede cursor overflow, then segment range errors; distinct
offsets are retained. Equivalent bounded copying and derived-safe casts replace
operations lacking useful pinned functional facts, without adding validation.

Four exact curated contracts bind these real producers without normalized
kernels, prepared step/coefficient banks or admitted budgets. The initial
pre-freeze supplemental whole-module check hit the unchanged shared-context
rlimit in existing packed-header reassembly; its original log is retained.
The standard existing fresh-query attribute resolves that query without
changing its executable body, caps, trust, pins or termination policy.
Independent u128/endian references compare 153,216 coefficient frontiers,
278,528 full-byte mutations, 917,504 descriptor/header contexts, 69,120 raw
step contexts and 5,760 complete payload/count/terminal contexts. Two maximum
encoded-count payloads contain 255 steps of 255 coefficients (1,040,929 input
bytes); 2,160 complete owner/budget cases and a real replacement reader join
check arbitrary prior registries and unchanged fields. These are maintained
native regressions, not official conformance.
Remaining fragmented transform/packet/layout/file/layer/F2/F4/final F8 joins
stay separate.

## Complete native raw TLM tile lengths

Actual TLM parsing binds its Result, complete parser and all eight extension
fields, and the external next-marker index. Real metadata/work charge runs
before header/index admission; index increment commits before style,
alignment and record admission. A matching byte index 255 advances to 256,
while subsequent mismatches leave it unchanged after charging.

Actual descriptor primitives derive optional 0/1/2-byte tile indices and
2/4-byte lengths. Source-derived alignment and standard Euclidean-remainder
lemmas establish every read/stride bound without admitted valid rows. Tile
bounds precede minimum length 14; each valid appended prefix remains after
a later row fails. Absent tile indices remain accepted at tile count zero,
and arbitrary existing length records and unrelated owners are preserved.

The curated complete contract binds all three mutable owners and raw inputs.
Equivalent explicit checked matches and remainder caching retain native
ordering without new normalization, result banks, trust, caps, solver budgets
or verifier pins. Remaining metadata/layout/file/layer/F2/F4/final F8 joins
stay separate.

Independent division/chunk/endian references compare 327,680 complete
header/style/index contexts, 131,072 external-counter contexts, 786,432
record-word contexts, 6,912 alignment/tile/length/prefix frontiers and 18,000
budget/three-owner cases. All comparisons include arbitrary existing length
entries and complete parser/extension fields. A real two-marker reader join
retains the first valid records and the second marker's committed index on
failure. These are maintained native regressions, not official conformance.

## Complete native raw nonlinear metadata

Actual NLT parsing derives every nonlinear descriptor field and the complete
parser/eight-field extension state from raw bytes, component count, limits
and arbitrary existing registries. The real shared charge executes first;
errors preserve its exact partial metadata/work commits without replacing a
registry entry. Successful parsing replaces only the first matching component
or default selector, leaving later duplicates and unrelated raw fields intact.

The sole actual payload body retains header/component/precision/type order,
four-byte identity/complement forms, five 24-bit gamma words with zero checks
only at positions 0/1/3, and LUT domain/count/bit/width/length/value ordering.
Stored point counts 1..8191 produce 2..8192 points; widths remain 1/2/4 bytes
and 32-bit point masks retain their special full-width case. All raw parameter
tail bytes are retained alongside decoded points and optional fields.

Actual tail copying and maximum-bit production have total functional
contracts. Existing precision/sign primitives replace equivalent safe
arithmetic, and standard array extensionality binds all five gamma words.
Loop invariants link real header admission to point errors and success, not
to supplied decoded records, parameter banks or normalized owners.
Five exact curated contracts bind these actual producers and both mutable
owners. No new trust, runtime cap, verifier pin, solver budget or termination
opt-out is introduced.

Independent endian/byte-fold references compare 524,288 selector contexts,
524,288 precision/type contexts, 15,360 gamma-byte mutations and 50 gamma
length frontiers. LUT checks cover 147,456 header/domain/count/bit/length
frontiers, 768 complete small-vector cases, 42 full 8,192-point cases and
384 value-cap/length precedence cases across all width boundaries. All 256
maximum-bit inputs, 39,936 raw tail contexts and 8,640 complete registry/
budget-owner cases are checked, including first default/specific duplicate
replacement and the actual reader join. These are maintained regressions,
not official conformance. Remaining metadata/layout/file/layer/F2/F4/final F8
joins stay separate.

## Complete native raw CAP and profile numbers

Actual CAP and PRF/CPF parsing now binds complete Results from raw bytes and
segment offsets. The real mask-count loop proves its exact 32-bit population
count and bound; the existing capability-length primitive consumes it.
CAP retains short-header, zero-mask and exact-length precedence. Capability
values remain raw, without new profile or marker policy.

The original identical word traversals share one executable body, preserving
big-endian order, vector capacity and checked next/read/push/advance order.
Its start bound comes from actual callers; an internal boundary guard makes
the shared helper total even for an out-of-range start, without changing any
actual parser outcome. Odd tails retain the original segment error offset.
Profiles retain nonempty/even length before checking
the last most-significant word, accepting leading and intermediate zeros.
Actual mask/word getters expose the complete raw owners without admission.

Four curated exact contracts bind both roots, actual word production and
bit counting. No prepared parsed-word/result bank, normalized-profile
premise, trust, cap, verifier pin or solver-budget change is introduced.
Independent endian/chunk/popcount references compare 917,504 word-reader
contexts, 524,288 profile-word contexts and 786,432 mask-half/length contexts,
plus 24 start frontiers, 730 profile-length frontiers and 2,652 CAP count/
length frontiers spanning every population count 0..32. They also compare
raw getters, complete unchanged parser fields and a real CAP/PRF/CPF reader
join. These are maintained native regressions, not official conformance.
Remaining metadata/layout/file/layer/F2/F4/final F8 joins remain separate.

## Complete native raw CBD component depths

Actual CBD parsing binds the complete parser Result and every parser/eight
extension-owner field from raw segment bytes, component count, limits and
prior metadata. The real metadata/work charge runs first. Count and exact
length admission precede clearing old depths; an invalid precision then
retains exactly the valid decoded prefix. Header and charging failures keep
old depths, including arbitrary raw entries. The real shared byte accessor
and existing precision/sign primitives supply every decoded field.

Repeated descriptors preserve expansion to the component count, including
the native one-entry outcome when the count is zero. A nonrepeated zero
count clears depths successfully. No new marker/scope/count/cap policy,
normalization, trust, solver budget or verifier pin is introduced.
Mathematical recursive terminal folds observe the sole executable loop.
Independent arithmetic/endian references compare 786,432 raw descriptor
contexts, 27,648 prefix/error-order mutations, 3,072 repeated-descriptor
contexts and 21,560 budget/header frontiers. Tests compare complete raw
owners and parser fields and join the actual byte reader. The curated
contract binds both mutable owners and all raw inputs; remaining
metadata/layout/file/layer/F2/F4/final F8 composition stays separate.

## Complete native raw DFS/ADS decomposition producers

Actual DFS/ADS parsing now derives decoded vectors and complete final parser/
extension states from raw segments, raw registries and actual metadata/work
limits. The real shared charge executes first and preserves every partial
error commit. No normalized registry, supplied decoded directions, successful
payload or admitted-budget premise is consumed.

The sole payload bodies are factored into stateless proved helpers. DFS
retains descriptor/reserved-index/depth/length order, depths 1..32 and its
permissive unused packed slots. ADS retains index 1..127, count-position and
length before packed-value admission, including zero raw counts. The actual
generic two-bit producer rejects zero depth codes before final padding while
accepting zero split codes; all reads and distinct offsets derive from the
real checked accessor.

Original first-matching registry replacement is implemented as an equivalent
bounded search, preserving later duplicates and appending absent keys. All
eight extension fields and every parser field are framed. Real unpacking
reuses the proved packed-bit primitive; remainder/shift bounds establish the
equivalence of the original wrapping mask subtraction and ordinary safe
subtraction. No new runtime validation, cap, trust, pin, solver budget or
termination opt-out is introduced.

Independent division/power/endian references compare 15,360 packed-byte
contexts, 245,760 unpack frontiers, 3,538,944 DFS payload contexts, 46,656 DFS
owner/budget contexts, 262,144 ADS count pairs, 153,600 ADS header contexts,
1,032,192 full-byte mutations and 62,208 ADS owner/budget contexts. Full raw
nested owners, duplicate order, DFS-unused bits and real reader joins are
checked. Five curated exact contracts bind payload and complete owner
results. Remaining metadata/layout parsing and outer file/layer/F2/F4/final
F8 joins stay separate.

## Complete native raw RGN/CRG component markers

Actual ROI and component-registration parsing now bind native Results from
raw segment bytes/offsets and component counts. RGN retains exact length
before index/style admission, the one/two-byte threshold 257 and every raw
shift byte, including 255. Marker identity and later shift execution policy
are not newly checked in this helper.

CRG binds the complete final parser and all eight Part2 extension fields on
both success and failure. The actual shared metadata charge runs first:
payload plus four bytes, checked metadata accumulation, metadata cap and
actual work charging. Overflow leaves the original relevant counter;
metadata-cap failure retains the increment without work charging, and work
overflow/cap retain the native earlier metadata commit. Length precedes
duplicate admission, all four-byte endian entries derive from source, and
repeated empty zero-component markers preserve the original empty-owner
behavior. Other raw metadata is neither normalized nor newly validated.

The real checked segment-byte accessor distinguishes cursor-offset
arithmetic errors from segment-offset bounds errors. Whole owned-extension
observations and exact prefix equalities frame every unrelated field.
The metadata getter is bound to its raw field through the canonical cap
model. No extra decoder, caller admission premise, trust, cap, pin or solver
budget is introduced.

Independent references compare 1,966,080 ROI word cases, 655,360 full
style/shift cases, 2,100 length frontiers, 1,080 accessor frontiers,
32,340 complete budget/owner cases and 131,072 full registration-word
contexts. Raw nested metadata fixtures, limit/overflow ordering and a real
reader join check actual partial commits. Five exact contract recipes bind
source/results and both mutable frames. Remaining metadata/layout parsing
and outer file/layer/F2/F4/final F8 joins remain separate.

## Complete native raw QCD/QCC quantization producers

Actual QCD segment/payload and QCC parsing derive complete Quantization
Results from raw bytes/offset, raw coding style and component count. Every
style/guard/count field and all 97 physical steps are bound, including unused
zero entries. The actual proved subband counter and component-index/word
producers supply their values; no normalized style, admitted count/header,
prepared steps or successful-result bank is supplied.

Empty input and low-five-bit style admission precede exact length, unscaled
low-bit traversal, capacity and checked step decoding in native order.
None, ScalarDerived and ScalarExpounded retain their exact exponent/mantissa
and count semantics, including all guard bits. QCC retains the 257 threshold,
component-error precedence and source-derived payload suffix. Marker checks,
scalar/reversible compatibility and limit policy remain at original callers.
In particular, main-header QCD-before-COD remains supported.

Opaque mathematical traversals bind real validation/array loops and every
error/offset. The existing proved malformed constructor and equivalent
explicit checked-result stages provide functional facts without a new
executable parser, trust, termination opt-out, solver budget or cap change.

Independent endian/division/modulo references cover 524,288 full-word
contexts, 1,966,080 header/length/direction contexts, 150,016 unscaled-byte
frontiers and 184,320 QCC prefix/error contexts, plus a real reader join.
All raw depth bytes and direction modes, each reserved style and every
physical/default slot are compared. Three exact contract recipes reject
adversarial input/result mutations. Remaining Part2/tile/layout parsing and
file/layer/F2/F4/final F8 joins stay separate.

## Complete native raw COC component-style producer

Actual component-index decoding and COC parsing derive their complete native
Result from raw segment bytes/offset, component count, raw default style and
limits. The one/two-byte threshold remains 257; truncation precedes the
component check and retains each caller's malformed kind. The COC helper
still leaves marker identity and DSC registry admission to its real callers.

Minimum length, SCOC flags and the nonzero DSC selector are admitted in their
original order. The original 43-byte COD scratch inherits progression,
layers, MCT and SOP/EPH; selected DSC replaces only its depth byte. Its sole
actual preparation body is factored into a proved private helper to isolate
the query, not duplicated or supplied by a caller. The complete real COD
producer is then executed, and only the decomposition selector is replaced
in its result. Every style field, all default directions/precincts, checked
error and offset are bound without a valid-default or prepared-payload bank.

The existing proved malformed constructor and equivalent explicit bool byte
encoding supply missing pinned standard-library facts. Checked overflow,
copy order, scratch capacity, public APIs, solver budgets, pins, resource
caps and the trust boundary are unchanged. Large new denotations stay opaque;
the real producer uses the repository's fresh-query isolation pattern.

Independent endian/numeric references check 5,242,880 component-index cases,
1,244,160 complete COC contexts and 132,480 length/error frontiers, plus an
actual reader join. The COD reference is shared with its existing regression,
not copied into production. Three curated exact contracts bind real source
inputs/results and reject adversarial mutations. Remaining Part2/tile/layout
parsing, file/layer/F2/F4 and final F8 joins stay separate.

## Complete native raw COD coding-style producer

Actual COD segment/payload parsing now derives complete CodingStyle Results,
including all 32 default decomposition directions and all 33 actual/default
precinct entries, directly from source bytes/offset/limits. Header/flag/
progression/layer/MCT/checked-u8 depth/resolution/block exponent/product/
style/length/precinct-capacity order remains unchanged. Raw transform indices
above one still yield arbitrary transforms; no registry admission is added.
Precinct capacity stays lazy, so otherwise admitted high depths without
explicit precincts retain their original behavior.

The actual shared Tier1 block-style body is called directly rather than its
unsupported pinned static facade; public APIs, masks and error translation
remain unchanged. Explicit checked stages preserve every malformed/resource
offset and first failure. Native arrays are tied extensionally to opaque
terminating byte-derived models without style/precinct/result banks or new
caller premises. A cfg(test)-only layer/resolution fixture does not change
production caps or public configuration.

Independent standard-endian/numeric-field references check 483,840 complete
raw Results, every header byte, block-size frontiers, unknown transform
indices, untouched defaults, raw depth/precinct capacity and an actual reader
join. Remaining quantization/Part2/tile/layout parsing and outer file/
F2/F4/final F8 remain separate.

## Complete native raw SIZ image producer

Actual `Parser::parse_siz` now derives a complete ImageSize/r_siz Result from
the actual raw segment payload/offset and limits. Every geometry/count/flag
and all 64 private component slots are bound, including unused zero entries
and registration defaults. The helper does not newly check marker identity:
its actual parser caller already enforces SIZ at the original earlier point.

First-tile checked overflow precedes expected-length/geometry admission;
component limits precede ordered precision/subsampling/capacity checks.
Uniform precision and sign remain the original paired sticky policy, so a
sign-only mismatch still clears both flags. Width, height, pixel and tile
admission follow all components in native order. Byte words, shared ceiling
and segment-offset malformed errors have actual complete contracts, as do
the four geometry cap getters. A literal matches the former derived zero
default array; no caller supplies normalized headers, descriptors or results.
Every loop/frame/bound is proved internally under an opaque terminating fold
with unchanged trust, pins, budgets and native policy.

Independent endian chunks and wide geometry/resource references cover
69,888 complete raw cases, 2,304 descriptor boundaries, 4,096 word encodings,
ceiling frontiers and an actual reader-to-SIZ join. A test-only raw geometry
limit fixture exercises otherwise non-public cap combinations and array
frontiers; no production cap or public configuration API changes. Remaining coding/
quantization/Part2/tile/layout parsing and outer file/F2/F4/final F8 remain
separate.

## Complete native raw codestream reader

Actual parser input admission and every raw reader operation now bind the
complete original bytes/limits/cursor/work/packet-counter observation and
Result, including partial error commits. Marker peek rejects stuffing/fill
without charge. Segment reading charges before order/length checks and
derives the exact payload slice from source. Standalone matching advances
before work admission; EOC scanning charges each candidate before using its
match and leaves a found marker unconsumed. Offset and overflow/truncation/
resource priority are retained for arbitrary raw cursors and counters.

The sole initializer is a free body for the pinned attribute mechanism.
Explicit checked-result matches expose the original arithmetic; replacing
the trailing-byte break with its identical final truncation return retains
all fields and error order. No parsed segment/layout/result bank, normalized
cursor, valid-input or budget-success premise is supplied. Actual header and
tile parser callers use these sole bodies; marker-specific metadata and whole
layout/parser-to-output/file/F2/F4/final F8 remain separate.

Independent endian words, wide counters, range decoding and window search
check every 16-bit marker, input admission and arbitrary cursor/resource/error
states, including exact reader fields and payloads after failure. This is a
real raw-byte producer milestone, not whole parser or conformance closure.

## Complete native full and selected typed layout decoding

Actual `typed_layout` now has a complete typed-image Result contract through
real decoded-to-typed conversion, source-derived nonlinear region collection
and complete owner mutation. Actual `decode_typed_layout` composes the genuine
full/selected parsed-layout byte/sample producer with that finalization and
the original final shape validator. Every typed geometry, descriptor, sample
and channel-definition field is bound; first errors and allocation/selection/
budget order are unchanged.

Both public raw codestream entry points still execute the actual byte parser
first, then use this sole private computational body. No supplied decoded,
typed, region or sample bank or normalized-layout/coverage/budget premise is
used. Only new top-level denotations are opaque outside their own producer
proofs to bound context. Maintained real-byte fixtures and raw layout/NLT/
selection/limit mutations cover 4,800 complete Results and 160 public-wrapper
joins. References compose previously independently qualified actual child
producers and a wide final-shape check, not provided successful outputs.
The compressed-byte parser itself still lacks a complete functional Result;
file/F2/F4/final F8 and delivery are not completed by this parsed-layout join.

## Complete native nonlinear owner mutation

Actual image and component region application refine complete Result/final
owner-state pairs, including errors. The real per-component computational
body uses actual source samples, derived None scratch, target and work;
the image loop commits exactly successful component prefixes. A failed
component retains every original field and channel definition. Geometry,
unrelated descriptors and definitions remain unchanged throughout.

Selected-region bounds and target consistency precede ordered row/pixel
address, duplicate, source and actual nonlinear scalar checks. A decoded
pixel precedes its original global work charge. After all regions, original
per-component decoded-byte admission precedes ascending coverage/conversion
checks and only then samples/precision/sign commit. Shared checked-index
and work helpers reuse the same proved operations and errors. No source
coverage, normalized image, scratch/sample/result bank or new caller premise
is supplied. Every internal frame and opaque fold termination is proved.
The existing LUT coordinate and signed-remainder computations are also
isolated into their actual proved scalar bodies, retaining all operation
order and complete contracts while bounding unrelated solver context.
Large interval-count overflow is exercised directly without allocating
an unrealistically large table; no solver budget or trusted boundary changes.

Independent map-based coverage, wide offsets/budgets and the separately
validated scalar reference check 7,056 whole-owner/error contexts, including
prefix commits, ignored malformed nonmatching regions, holes, overlaps,
byte/work priority, raw shapes/descriptors and preserved metadata. Raw
initial-work overflow and the original 65,536 component narrowing frontier
are exercised without large sample allocations. Whole typed/parser/file/
F2/F4/final F8 and delivery remain separate.

## Complete native nonlinear sample producer

Actual `inverse_nlt_sample` now refines the complete raw sample/component/
transform Result for all supported and unknown kinds. It composes genuine
parameter decoding, three gamma branches, checked log/exp/reciprocal, LUT
interpolation, binary complement and the original final target-range check.
Every error and value derives from actual raw fields, not supplied parameter,
curve or sample results. Descriptors are not normalized or newly validated.

The sole private free bodies preserve pinned attribute support and actual
region consumers. The former parameter callback becomes one proved body;
the real gamma curve is isolated under an opaque proved model. Top-level
gamma and dispatch denotations are also opaque outside their actual producer
proofs, preventing unrelated queries from expanding their context; complete
bodies and Result contracts remain unchanged. Source and
target precision/scale order, checked intermediate overflow, fractional
denominator 65535, signed rounding and unknown-kind behavior remain unchanged.
No caller premise, trust, tolerance or solver/iteration change is introduced.
Tests cover 393,216 parameter encodings, 20,384 raw gamma and 45,864 full scalar
contexts, plus raw curve frontiers. Gamma references share independent
unsigned-magnitude/flat-series calculations; full dispatch reuses the
separately independently tested, proved LUT child. No analytic accuracy or
official conformance claim is made. Region application/whole typed/parser/
file/F2/F4/final F8 remain separate.

## Complete native fixed logarithm and exponential

Actual fixed logarithm, exponential and reciprocal-power Results now compose
the real two-pass normalization and ordered 20/24-term native series. The
128-ticket normalization counters, all checked arithmetic, Q32 rounding,
scale range and signed shift/error policy are unchanged. All raw inputs,
including zero/negative logarithms, are covered without the former positive
logarithm caller premise; native failures still arise from the original
checked operations and counters.

Sole private free bodies preserve pinned attribute support. Actual
normalization and series helpers derive their full Results under opaque,
terminating folds; no normalized input, successful series or result bank is
supplied. Constants are proved before their first checked use. Redundant
LUT diagnostic assertions are removed while its complete Result contract stays
unchanged; explicit checked remainder retains the same native operation.
No budget, tolerance, iteration count or trusted adapter is changed.

Independent bit-length normalization, shared unsigned-magnitude arithmetic
and flat ordered folds check 762 signed power-neighbor contexts, 645 scale
frontiers, 405 raw log series and 100 reciprocal pairs, plus raw extrema and
exact fixed-point identities. This proves the existing bounded computation,
not analytic convergence or a standards accuracy claim. Gamma/whole scalar
dispatch/region/typed/parser/file/F2/F4/final F8 remain separate.

## Complete native nonlinear LUT inverse

Actual `inverse_nlt_lut_sample` refines a complete Result from the raw source,
component descriptor and transform. Precision/minimum/maximum/point-count/
source admission order remains explicit. Registered descriptor fields and
unrelated transform kinds are not newly validated. Source offset, clamping,
checked interval scaling/conversion, endpoint or ordered point reads, signed
Rust division/remainder, interpolation and signed/type4 remapping preserve
all original errors. Nonmonotone and out-of-target-range raw tables remain
accepted here; the outer scalar dispatcher retains its separate final check.

The private receiverless body is a sole module function for pinned attribute
support. The actual position and interpolation arithmetic are extracted once and proved
under opaque mathematical bodies to isolate nonlinear solver context without
raising budgets. The position helper explicitly rejects empty private inputs;
the real producer already rejects fewer than two points at its original
earlier transform check. Interval-count conversion uses unsigned widening followed
by the original signed bound before narrowing; every read/increment frame
derives internally. No supplied table/sample results or validity premises
are used. An independent unsigned weighted-endpoint reference covers 314,496
raw descriptor/sample contexts plus intermediate overflow frontiers.
Gamma/log/exp, whole dispatch, region application and typed/parser/file/
F2/F4/final F8 composition remain separate.

## Complete native nonlinear scalar arithmetic

Actual ratio rounding, bounded power-of-two and Q32 multiply/divide refine
complete mathematical Results for every raw input. Intermediate overflow is
not bypassed even when a final quotient could fit. Ratio ties round away from
zero, negative Q32 division truncates toward zero, MIN negation rejects, and
invalid division denominators retain their distinct transform error. Native
exponents above 38 still reject. Ten actual NLT getters expose every raw
descriptor field without adding validation.

These four private receiverless bodies are module-level functions because
the pinned attribute mechanism cannot bind associated static receivers.
Every computational caller uses the sole moved body; public APIs and
allocation/error order are unchanged. Explicit checked-result matches expose
the original arithmetic stages to Verus without trusted callbacks or new
input premises. Power-loop bit facts are proved at the original budget.
Unsigned-magnitude references cover 35,535 small ratios, 729 boundary pairs
for all three binary operations, every u8 exponent and 180 raw descriptors.
Whole log/exp/LUT/gamma/dispatch and region/typed/parser/file/F2/F4/final F8
remain separate work.

## Complete native nonlinear region production

The actual `Part2Extensions::nonlinear_transform_for` refines first specific,
then first default selection over complete raw transform observations. Two
explicit scans preserve the former iterator order without trusting callback
results or normalizing descriptors.

Actual `typed_layout` uses the single extracted `nonlinear_component_extent`
and `collect_nonlinear_regions` bodies. Their complete Result contracts derive
every ordered region and transform from the actual raw layout and typed image.
Last matching tile-part metadata replaces main metadata, including an empty
registry; no-match retains main metadata. Registration and checked extents
precede tile traversal; each tile narrows before lookup, and geometry is lazy
until a transform exists. Regions clip to the output and retain all source
transform fields. Empty components still bypass otherwise invalid metadata.
All loop/read/narrowing frames derive internally; no supplied regions,
transforms, successful results or valid-image premises are used.

The extraction preserves allocation, mutation and error order. A private
extent alias keeps the existing tuple shape within strict Clippy conventions.
Independent exhaustive-u16 selection and wide-coordinate/reverse-owner tests
exercise raw metadata, complete regions and first errors. Nonlinear sample
execution and full typed/parser/file/F2/F4/final F8 joins remain separate.

## Complete native typed output-shape admission

The actual `validate_part1_output_shape` refines
`part1_validate_typed_output_shape` from raw input length, actual layout and
typed image. Header/count/extent admission precedes ordered checks of every
signed or unsigned plane. The original division/remainder area checks avoid
multiplication overflow; descriptors, origins, channel definitions and sample
values remain uninspected. Every loop, read and increment bound is proved
internally without a valid-image or successful-decoder premise. Both public
codestream entry points still call this single unchanged executable body.
This closes the final shape consumer only, not typed nonlinear finalization,
raw parsing, file/F2/F4/final F8 or hosted/main/publication acceptance.

## Complete native packed-header and packet-length input producers

The actual `PackedPacketHeaders::reassemble` refines
`part1_packed_header_reassembly` over its complete raw source, stored length and
fragment count. The model preserves cap-before-None admission, all marker and
slice checks, the exact selected bytes, late malformed markers even after the
requested bytes were copied, and final output-length errors. Fragment count is
metadata, not an assumed physical-segment count.

The actual `PacketLengths` getters and iterator constructor retain the full raw
None/PLM/PLT source and both stored counters. `PacketLengthIter::next_length`
refines `part1_packet_length_next` on every raw cursor/end pair. Its PLT scan
commits the segment end before validating the payload start, and a later decode
failure retains earlier marker/cursor commits. The actual base-128
`decode_packet_length` has a complete Result contract, including zero,
noncanonical leading groups, truncation, five-group overflow and invalid windows.
Successful native iterator results additionally prove a positive value and a
strictly advanced cursor.

These are real production operations, not supplied byte vectors, length lists or
traces. The loops, allocation points, arithmetic order and typed caps remain
unchanged; explicit checked-result matches expose the existing first errors.
Marker words reuse the same production `refinement::marker_value` primitive.
Independent exhaustive two-byte/window/raw-iterator fixtures, closed wide-word
oracles and literal segmented inputs check whole results and partial-state order.
This does not complete the consuming progression/reassembly orchestration.

## Complete native palette lookup boundary

The actual `jp2::Palette::value` returns exactly `part2_palette_value` on its
private stored entries, complete physical column descriptors and value sequence,
for every native entry/column pair. No parsed-header, rectangular-table,
valid-coordinate or successful-lookup premise is imposed. Actual physical column
count conversion is checked before logical coordinates, followed by checked
row-major address computation and physical value access. Invalid descriptor
precision/sign does not itself make this raw lookup fail.

The stored representation stays private behind its owner view and exact public
getter contracts. Explicit matches retain the original conversion/multiplication/
addition/error order while exposing every real error, rather than relying on
uncontracted callback results. The shared local error producer is verified, not
trusted. Independent tests cover 8,820 complete supplied-state/native-coordinate
contexts, signed extrema, physical stride and first-error priority. The source
index binds the full Result, actual owner view, entry and column, with negative
tests for wrong, partial, unrelated and reordered bindings.

This raw lookup result alone does not establish palette parsing, source-sample
interpretation or composition with selected pixels.

## Complete native component copy and palette mapping

The actual `decode::copy_typed_component` and `map_palette_component` now have
unconditional complete Result relations. Copy preserves every metadata field,
signed/unsigned sample and ordered channel definition, including duplicates and
malformed source geometry. It does not invent validation of its inputs.

Palette mapping checks the actual selected column and precision before sample
access. Native signed/unsigned indices must fit `u16` and the stored entry
count before raw table lookup. Every stored value must fit the selected signed
or unsigned precision. Source geometry, subsampling and registration are
preserved; precision/sign and the sample tag come from the descriptor, and
incoming channel definitions are cleared. Empty input still checks the
descriptor but does not access or validate unvisited table storage. All
arithmetic, logical versus physical table and range errors retain their actual
order/category/offset. No parsed/normalized/rectangular/success premise is used.

The existing static component constructor API delegates to one verified free
production constructor, which the proved callers use directly. This preserves
the API and a single executable field-construction body while avoiding the
conditional frontend's static-impl contract limitation. Full mutable
channel-definition frames preserve component samples and metadata.

An independent wide-integer oracle checks 37,632 complete supplied contexts,
including invalid metadata/sign tags, integer extrema, empty/malformed tables,
descriptor boundaries and error precedence. All 256 native precision values
are checked separately. Five exact result/model/input recipes reject unrelated,
partial, reordered and constant bindings. Existing sparse-magnitude arithmetic
also explicitly instantiates its original final-limb premise to stabilize the
joined proof; no theorem domain, native algorithm, trust or limit changed.

Whole-header selection and final admission have a separate complete relation
below. Parser associations and selected-pixel composition remain separate F7
closure obligations.

## Complete native output-header and image admission

The actual `decode::apply_jp2_output` now returns exactly
`part2_apply_output_header` for every native typed image, supplied header and
actual component/decoded-byte caps. Empty CMAP copies all components; otherwise
the actual mapping vector selects sources in order. Direct mapping retains
existing CDEF; palette mapping clears it before the actual ordered header CDEF
records are appended. Duplicate records and unnormalized associations are
retained. The first invalid source uses the image-index error, whereas a missing
palette, invalid palette descriptor or out-of-range CDEF channel uses the
container-mismatch error. Earlier mapping errors precede final image admission.

The one executable `typed_image_from_components_with_origin` body is shared
with the existing `TypedImage::from_components_with_origin` API. Its full result
checks x/y origin addition, native u16 count conversion, component cap, then
each actual component's area/cardinality and cumulative eight-byte sample
charge, in production order. It preserves every sample, tag, metadata field
and CDEF record. Precision, subsampling, sign/tag agreement, image/component
dimension agreement and unused header image/color/count hints are not newly
validated. The actual borrowed `TypedImage::component` has an exact result
relation too. Explicit enum error construction and checked conversion matches
retain the original native behavior while exposing complete error payloads.

An independent whole-header oracle compares 15,624 supplied contexts, including
malformed native shapes/tags/metadata, absent palettes, duplicate definitions,
ignored header count hints, origin overflow and tight byte caps. Separate
admission regressions cover 64/65 and 65,535/65,536 component thresholds and
first-error priority. Three exact producer/model/input recipes reject partial
results, wrong owners/caps/inputs and a wrong primary clause followed by a
correct duplicate. Method resolution searches all formatted impl blocks of
the exact owner and rejects ambiguity, foreign owners and nested functions.
These are actual supplied-header results, not parsing/association, compressed
decoding, target derivation or whole-F7 completion claims.

## Actual native MCT dependency rows

Both actual dependency row producers have complete unconditional native
value/error contracts over full collection matrix/offset values, source
samples, source precisions, prior output and row. The real reversible row
preserves positive-scale admission and negative-remainder floor correction;
the irreversible row preserves nearest-magnitude Q32 rescaling and actual
precision overflow. Their different checked triangular indexes and lazy
None/row-zero branches are not normalized into a common valid-matrix premise.
Existing checked arithmetic and first-error order remain unchanged.

Both loops use the already shared complete dot-prefix/error-absorption proofs.
The positive reversible triangle bound follows from actual row-zero rejection,
not a public precondition. Native tests compare independent Euclidean-floor
and rational Q32 references, all256 precision tags, ignored raw metadata,
malformed arrays and exact source/offset/late-sum error frontiers. This is a
bounded row milestone; actual mutable collection/dependency/wavelet/stage and
whole reconstruction composition remain open.

## Actual native decorrelation row computation

The real decorrelation pixel loop now calls one proved row dispatcher and one
proved ordered row-append loop. The dispatcher includes both matrix branches
and both lazy None branches over the complete native source/precision domains.
It retains source-before-precision-before-offset error order, nearest-magnitude
Q32 rescaling, checked i128 addition and final i64 conversion. The sole native
arithmetic bodies are shared with the existing matrix-row producers.

The row-loop relation includes every initial scratch value and every value
appended before the first error. Empty row ranges perform no validation; later
failures preserve earlier output rows. The original scratch vectors, capacity,
clear order and all-rows-before-component-stores policy remain intact. An
explicit early-return loop invariant retains the real old scratch sequence,
not a supplied result or normalized input premise.

Independent tests cover all256 precision tags, signed sample extremes, lazy
None paths and partial scratch output. Actual collection regressions additionally
check duplicate destination overwrite order, prior-pixel writes on a later
numeric error, no current-pixel stores before every row succeeds, final-only
precision updates and exact charged work. These tests do not replace the still
open whole collection/dependency/wavelet/stage composition proofs or qualify
general MCT against an independent external oracle.

## Complete actual native decorrelation collection

The original `apply_mct_decorrelation` now has one unconditional full
Result/components/work relation over the original raw component/collection
values and actual limits. It calls the real preparation producer, derives
the real index/precision plan and charged work, then composes every actual
pixel and the final destination precision updates. There is no supplied
success, plan, normalized layout, admitted budget or decoder outcome premise.

The real pixel body clears both original scratch vectors, gathers every
source sample before computing any row, computes every row before starting
destination stores, and retains the actual ordered duplicate overwrites.
Its complete relation includes both scratch vectors and every partial
component update on an error. A failed source read or row leaves components
unchanged for that pixel; a later destination-store error retains prior
stores. Earlier complete pixels remain on later failures. Final precision
updates execute only after all pixels and retain their own ordered partial
error states. Unselected components, geometry, metadata and samples remain
in the full deep state relation.

Independent raw pixel fixtures exhaust 972 source/destination/row/sample
contexts, including duplicate aliases, missing components, unequal sample
lengths, contradictory unused plan metadata and sentinel scratch data.
Another1792 cases cover all256 destination precision values and partial
tag errors. Existing actual collection fixtures retain late numeric errors,
prior-pixel writes, duplicate destinations and exact work. This closes the
native decorrelation collection producer, not the complete dependency/wavelet
collections, stage traversal, general MCT/reconstruction or independent
external-array qualification.

## Complete actual native dependency collection

The original `apply_mct_dependency` now refines a complete unconditional
Result/components/work model. Checked triangular coefficient counts, raw
matrix/offset shape, interleaved source-then-destination lookup, original
per-component integer/layout validation, reversible array precision and actual
work/saturating-scratch admission retain their original order and first errors.
The real preparation returns actual indexes/counts without supplying a valid
plan or adequate budget as a premise.

The existing source/output/fraction scratch allocations retain their order.
Every pixel uses the same actual source-snapshot and ordered-store bodies as
decorrelation, with the dependency path's explicit count rather than silently
substituting the index-list length. Its real row loop feeds all previous
computed rows into the verified reversible floor or irreversible Q32 producer.
All rows finish before component stores. Cached original precision values,
duplicate references, prior-pixel writes, partial errors and final-only tags
remain in the full relation; no trace or row outcome is supplied.

Independent tests cover 22 coefficient overflow frontiers, 4320 wide admission/
counter/cap combinations using actual hardened limits, 4608 destination-precision/
exact-cap preparation cases, 216 whole floor/Q32 collection contexts and 972
raw pixel/count/duplicate/error states. The initial test attempted an invalid
above-hardened limit and failed explicitly; that log is retained, and the
corrected test uses only the repository's real immutable caps. Wavelet
collections, stage traversal, complete reconstruction and coherent integrated
qualification remain separate work.

## Complete wavelet, stage and real owner-buffer MCT composition

The actual wavelet collection now derives its complete plan from the real
wavelet descriptor and original component values. Signed half-ceiling,
forward interval/parity partitions, reversed synthesis levels, real 5/3 and
9/7 calls, source precision scaling, final cardinality checks, stores, tags,
work and scratch errors have complete relations. The wavelet transform enum,
not an assumed agreement with the collection's reversible flag, selects the
actual path. Source scaling remains interleaved with reads so an earlier
numeric failure is not masked by a later missing source.

The original component coordinator now composes all three real collection
kinds, forward collections within each stage, and stages in reverse order.
Every subset, duplicate identity, prior mutation, charged counter and first
failure is retained. No stage or decoder outcome is provided to the model.

The owned-image API and actual prepared-tile consumer now compose through
their real borrowed component vectors. Their recursive collectors prove
current input values, exact partial extents and final-field alias promises;
all mutating MCT phases preserve those promises. Prophetic specifications
describe actual borrow endpoints, not trusted adapters or assumptions.
Prepared-tile metadata lookup failures leave every owner buffer and the work
counter unchanged. Static private helper bodies moved to proved free functions
to avoid the pinned associated-static attribute inference limitation; both
production call sites use the same sole executable bodies.

Prepared standard RCT/ICT now also has complete admission/pixel/traversal
relations and uses the already proved actual scalar component transform
instead of a second arithmetic implementation. Disabled transforms still
skip validation; geometry, raw fractional tags, prior successful pixels and
all error states are preserved.

The actual `reconstruct_planned_tile` now composes raw planned coefficient
values, coding-style lookup, first-match kernel selection, ROI/quantization/
inverse preparation, optional complete MCT and standard RCT/ICT into one
Result/prepared-vector/work relation. Both full and selected decoder paths use
that same body. `assemble_prepared_components`, `decode_prepared_image` and
the public supplied-progression reconstruction API close the real borrowed
tile/full-selected assembly joins. No decoded coefficient or transformation
outcome is supplied to these models.

Fifteen finite exact reconstruction shapes preserve all old/final owners,
input projections, caps and selection parameters. The two standalone public
MCT/progression APIs are checked through an explicit proof-support whitelist,
not fabricated internal consumers. Negative mutations and all original packet
checks remain enabled. Coherent main/hosted acceptance, independent array-MCT
conformance and whole-project completion remain separate.

## Complete actual MQ and legacy three-pass producers

The actual MQ decoder now refines [a complete state model](specs/mq.rs):
input bytes, physical position, interval/code/count registers, all nineteen
probability contexts and MPS bits, work counter/cap and marker-padding counter.
The independent forty-seven-state probability sequence is joined to the real
table. Decode includes both conditional exchanges, real context transitions,
byte stuffing, bounded renormalization and the real first error. Input admission,
context save/restore/reset, byte consumption and predictable-termination checks
have their complete relations too. No initialized-register, valid-context,
valid-stream or sufficient-budget premise restricts the decoder methods.

The actual legacy significance-propagation, magnitude-refinement and cleanup
passes refine [whole pass/state models](specs/legacy.rs), including both MQ and
bypass readers where the production entry permits them. All four subband
orientations, causal-context choices, cleanup run interruption, delayed symbol
statistics, segmentation symbols, six coefficient words, sign/refinement/
legacy-bitplane flags and both complete bitplane-state vectors are represented.
Public with-style entries observe the style fields actually used by each pass;
they do not silently validate other fields. All errors retain actual reader,
coefficient and visit-flag mutations. Completing a pass is not transactional.

The stripe/column/row traversal and cleanup run-mode skipping remain intact.
Their existing coefficient operations have one production implementation;
private cell/column/row stages expose its state transitions. A private static
reader adapter delegates directly to the actual MQ or raw reader. Its ghost
view has concrete implementations for both readers, not a supplied symbol
trace. Existing static constructor APIs delegate to verified free constructors,
following the pinned frontend's established static-impl limitation.

Independent tests exhaust all two-byte MQ initializations, native context-state
bytes and both MPS values; assert complete register/context/error effects;
exercise all 65,536 native legacy sign bitplanes; and check actual three-pass
composition and every raw cleanup/run/segmentation-symbol budget prefix.
Native reference-decoder qualification remains a separate gate.

This entropy and three-pass producer boundary alone is **not F5L**. The
segment/contribution composition below closes its next actual callers; packet
association and whole-decoder transactional composition remain distinct.

### Faithful raw legacy clone prerequisite

`CodeBlockPlane`, `Tier1BitplaneState` and retained `LegacySegmentState` now use
explicit faithful `Clone` implementations with unconditional complete raw-view
postconditions. Their field order and each original `Vec::clone` allocation
remain unchanged. These are data copies, not validated-plane duplication:
zero/extreme geometry, mismatched vectors, non-normalized words and arbitrary
flags/tags are preserved exactly. Independent mutation tests cover 1,600 raw
source families with both absent and present retained bitplane state.

Both whole-decoder and retained-legacy ghost frames use the same logical
eight-field bitplane projection and full nineteen-context snapshot projection.
They no longer treat non-Copy cloned vectors as opaque native identity.
This supplies actual data-copy facts to staging proofs. It does not itself
establish the shared whole-decoder clone or dispatcher.

### Actual legacy segment and retained-contribution composition

Contribution admission isolates its existing checked numeric work charge in
`legacy_contribution_work`, then explicitly frames the sole work-counter commit.
The complete caller contract and native error/commit order are unchanged.
This real phase decomposition avoids exposing whole coefficient/context frames
inside scalar multiplication queries; it does not increase verifier limits.
Independent wide-integer fixtures cover native extrema and arithmetic-before-cap
error priority.

The actual `decode_legacy_segment` now has an unconditional complete Result and
whole-decoder-state relation, using actual MQ/raw construction, all three pass
producers, pass scheduling, advancement, context initialization/restoration/reset,
termination validation and final accounting. Every native pass count, coding
style, coefficient/state vector, retained context and real owner cap is admitted.
The ordinary MQ and selective-bypass profiles, including reset, terminate-all,
causal, predictable-termination and segmentation-symbol controls, use the actual
style operations; no valid parsed coding-style/header premise is supplied.

The actual `decode_legacy_contribution` then composes resource admission,
retained-prefix selection/take, faithful snapshots, concatenation, restoration,
real segment replay and retention. Its model observes the complete original
retained record, not a supplied decoder result. The replay-work estimate is
charged at its actual position before the later pass-addition check. Taking a
retained record and restoring its starting state precedes the real replay:
errors can therefore retain charged work and a restored prefix while consuming
the retained record. These internal operations are deliberately **not**
transactional. Final segment/byte commits also precede the real `u32` byte-count
conversion, preserving those partial effects on conversion failure.

The existing loops and operation order are preserved in real admission,
pass-loop, append, restore and commit stages with complete contracts; opaque
mathematical phase boundaries only control unfolding. No extra codec, decoder
algorithm, tracing input, proof budget or resource default is introduced.
Independent whole-state tests cover an actual complete MQ cleanup block, raw
pass pairs, predictable-termination and work failures, retained replay versus
whole contribution, late replay-input rejection, accounting overflow and
full-width pass-index/style boundaries. Unvisited HT state is framed too.

Packet-facing route/pass/accounting getters and the actual zero-bitplane setter
also have unconditional owner relations. A previously stored equal zero-bitplane
value succeeds before checking phase/counters; a different value fails first.
The original checked multiply/add calculation is isolated once, retaining its
complete native `u16` range (including values beyond the supported bitplane
ceiling), arithmetic order and the setter's original field-commit order.

The foreign packet caller is
`packet::decode_code_block_contribution_body_staged`, whose legacy loop invokes
this exact contribution producer on each checked body slice. Its enclosing
`decode_code_block_contribution_body` performs actual clone/commit staging.
Those packet contribution associations, ordered final consumption/pass-total
checks, full transactional caller result, header classification and mixed
HT/legacy dispatcher union remain owner closure obligations, **not completed
F5L**. That producer stage did not change packet/decode/image/transform
implementations; the subsequently authorized packet owner prerequisite follows.

### Shared native contribution lookup prerequisite

The sole `packet::code_block_contribution_view` now exposes all five public
fields, the stored count and both complete 164-element pass/length arrays.
The actual count getter returns the stored byte unchanged. The actual segment
getter refines `part1_code_block_segment` over every native count/index pair,
including stored counts above the physical array size. Count admission precedes
physical bounds; failures remain `InvalidPacketHeader` at offset zero. No
header, pass-total, nonzero-pass or normalized-count premise is introduced.
Independent tests cover all 65,536 count/index pairs and preserve the entire
supplied record. This owner interface alone does not establish packet execution;
the actual legacy loop is composed below, while HT routing has a separate owner.

### Shared native contribution preparation

The actual `prepare_code_block_contribution_body` refines the unconditional
`part1_code_block_body_prepare` Result/full-decoder-state relation. It preserves
the original conversion/exact-length, route-admission and zero-bitplane-setting
order, using the actual proved owner operations. Both offset-zero error producers
are verified. The existing checks are moved once, without adding validation,
allocation, resource limits or a second packet decoder.

No parsed-header, normalized segment count, pass-total, success or budget premise
is supplied. Independent whole-state tests exercise every length/force/route/
zero-bitplane choice in the selected boundary set while deliberately retaining
unvalidated 255-count/255-pass descriptor storage. This shared prerequisite
establishes preparation only; packet execution and outer clone/commit remain
separate caller obligations.

### Complete selected native HT packet contribution body

For the sole contribution view's `high_throughput` selector, the actual staged
and public transactional packet-body functions now refine
`ht_packet_body_staged` and `ht_packet_body`. These are conditional
postconditions selecting an actual branch, not header-validity preconditions.
The actual common preparation producer is reused. Complete native descriptor
storage, arbitrary prior decoder state, body bytes and actual pass/byte/work
caps remain inputs; no decoder result, successful trace or legacy outcome is
supplied.

`run_ht_contribution_segments` is the original actual HT traversal, not a second
decoder. Its exact relation retains segment index, native offset and decoded
pass count alongside the complete decoder. Every lookup, pass/length/address/
slice failure and per-segment decoder effect is ordered. A late local counter
failure preserves already committed decoder effects and the old offset/count;
final consumption/pass-total failures preserve the staged decoder. The public
function uses the actual faithful whole-decoder Clone and commits only on
success, preserving every original field on failure.

The independent regressions include real cleanup slices, late accounting,
zero-setting before empty-count rejection, final pass mismatch, successful
placeholder grouping, and a stored count of 165 reaching physical entry 164
after 164 actual placeholder steps. Mathematical properties additionally prove
first pass-error preservation, completed-loop framing, exact successful result
counts and complete error rollback. The immutable legacy else-selector is
retained only by a ghost invariant; no legacy runtime or outcome claim is added.

This closes the selected HT contribution-body boundary. It does **not** close
the shared header parser, the full HT/legacy dispatcher union, precinct/packet
orchestration, normative endorsement or the whole F5H epic. Those must consume
their actual owner producers rather than assumed outcomes.

### Actual legacy contribution-body execution

The actual `decode_legacy_code_block_contribution_body` now refines a complete
unconditional Result/full-decoder relation. It runs the original stored-count
loop, performs each real physical descriptor lookup, computes and checks the
actual body slice, invokes the proved actual legacy contribution producer and
commits pass/offset/index counters in their original order. The one real
per-segment operation exposes all four partial outputs: decoder, segment index,
body offset and decoded-pass count. Native overflow, physical-array and range
failures retain their actual priority; no header or successful-segment trace is
supplied to the loop theorem.

The final exact-consumption and pass-total checks follow all decoder effects.
A late mismatch therefore preserves the already decoded state inside this
operation. The stored `data_length` is returned, not silently replaced with the
consumed count. Empty zero-pass storage can succeed here, since shared header
preparation belongs to its actual caller. Those unvalidated native cases remain
in the model instead of being excluded by a normalized-contribution premise.

The shared prefix and the original HT branch are not duplicated by this
extraction. Independent tests cover real MQ bytes through the full legacy call
chain, late total mismatches, physical lookup before range overflow, pass-counter
overflow after actual decoding, shared preparation and observed public rollback.
The coherent owner join now supplies the actual faithful whole-decoder Clone.
Both the actual staged caller and public `decode_code_block_contribution_body`
refine their complete legacy-profile Result/full-state models. The profile is
the actual `!contribution.high_throughput` branch selection, not a valid-header,
successful-decode, normalized-state or adequate-budget premise; every other
native descriptor/body/decoder/cap input remains admitted. Public errors leave
the original entire decoder unchanged, while successful staged output is
committed. The real shared preparation and actual legacy packet loop produce
the staged outcome; no clone trace or supplied legacy outcome is an input.

The one true-selector invariant in the still-inline HT loop only retains its
actual immutable branch guard for that disjoint legacy-profile result. It
changes no runtime operation or HT effect. This closes the selected legacy
packet-body-to-coefficient call chain. The combined HT/legacy public packet
relation, header parser/retained packet associations and full-codestream joins
remain separate owner/integration obligations; this is not all of F5L.

### Complete unconditional mixed contribution-body and Tier-1 dispatch

The two actual packet route families now compose through one unconditional
`part1_code_block_body_staged` relation: actual shared preparation, then the
actual descriptor's HT selector, then the corresponding complete native helper.
`part1_code_block_body_transaction` composes the actual faithful decoder Clone
and commits only on success. The existing selected HT and legacy postconditions
are retained as consequences of this full relation, not supplied outcomes.
There is no header, decoder-shape, success, trace or adequate-budget premise.

The obsolete selector-only loop frames disappear because both real loop helpers
are used directly. All HT helper bodies are byte-identical to frozen `feddd4a`;
both legacy helper bodies are byte-identical to frozen `7827a1b`. The public
transaction's runtime body, shared preparation, error factories and allocation
order are unchanged. No duplicate executable decoder or algorithm is added.

The existing actual `Tier1CodeBlockDecoder::decode_segment` dispatcher also
refines unconditional `part1_tier1_segment`: pass-zero rejection first, then
the actual HT/Mixed-with-stored-cleanup-option selector, otherwise the actual
complete legacy segment producer. Its native body and the primitive producers
are unchanged. A cleanup option is not replaced by the current-cleanup flag.

Independent mixed-style tests use literal MQ/HT bytes and coefficient values,
empty-count asymmetry, late final-total failures and full original-state rollback,
the distinct actual input-budget policies, and the stored-cleanup-option selector.
Properties prove preservation of both selected profiles, first preparation
failure, full transactional error framing and native Tier-1 route order.

This closes these mixed native body/segment boundaries only. Actual shared
header parsing, retained packet associations and complete precinct/packet
orchestration still require their own complete producer contracts. It is not
normative endorsement or whole-epic completion.

## Complete native header primitive boundaries

The continuing native header thread supplies complete packet-reader and raw
TagTree producer relations before closing header parsing. `packet_bit_reader_view`
observes all eight fields, including both actual caps and stuffing history.
The real validated constructor and unchecked-prefix constructor remain distinct:
the latter admits the entire packet storage but checks the header-byte cap at
each actual load. Reads preserve exact error priority and partial consumption.
Zero-width words still succeed on otherwise invalid native reader states.

`tag_tree_view` observes every raw level and node without topology, offset,
monotonicity or normalized-value premises. Actual path construction retains its
64-level/address guards; node and reverse traversal use the actual reader and
preserve inherited-low writes on later read failure. Duplicate node addresses,
empty/malformed levels and `low > value` remain admitted by the full native
Result models. The actual constructor preserves ordered level/node admission.
A faithful raw Clone supplies the real higher JPIP rollback copy, not a validated
tree replacement. Reader/tree/packet-state constructor APIs delegate to one actual free
producer body under the pinned static-impl-contract frontend limitation.

Packet-state owner/getter contracts preserve all five native fields. One public
Option/Result projection maps actual contribution storage while keeping `None`
and `Some(empty)` distinct. Independent tests cover all two-byte inputs and
complete final reader fields, raw threshold/budget states, duplicate 64/65-level
paths, address-error priority, constructor rectangle/cap boundaries and every
native Lblock byte. These primitive boundaries alone are not a full header claim;
their actual header/probe/rollback composition follows below.

## Actual full native code-block header production

`decode_code_block_contribution` now has an unconditional complete
`part1_packet_header_decode` relation. It observes the full packet state, both
raw TagTrees and all eight reader fields, and maps the entire optional native
contribution through the sole owner projection. It runs the real inclusion and
zero-bitplane trees, pass grammar, Lblock flags, descriptor reads and final
commit. No valid header, normalized tree/packet state, supplied descriptor or
successful/sufficient-budget trace is a premise.

The actual Mixed probe forks the complete native reader before the first length
read. A failing probe returns its real error while retaining the main reader's
already-read HT prefix. Successful unselected probes do not charge or advance
that main reader. A selected legacy probe is committed only after the actual
accounted-pass check; all packet-state and routing effects retain their order.
The descriptor loop keeps all 164 physical slots. Its mathematical attempt bound
is derived from those actual slots plus the first failing capacity check, not a
new native count restriction or proof-budget change. Raw private 164/165-count
and post-commit conversion cases remain explicit.

The public packet state is unchanged on every header error, as proved from the
actual local state copy and guarded final conversion. Tree/reader changes before
the error are deliberately retained. A first unincluded header returning `None`
differs from an already-included empty contribution. Existing malformed zero
tags and all Lblock bytes are admitted until an actual executed guard rejects
them; unvisited trees are not invented validation obligations.

Independent whole-result/owner-state fixtures cover literal encoded headers,
every budget cutoff, both real probe choices and discarded probe failures,
all stored Lblock bytes, empty/unvisited raw trees, late pass admission,
physical descriptor-capacity priority and final state-commit/conversion order.
This completes the actual header producer boundary, not precinct/progression,
header-to-codestream association or all F5L/F5H.

### Actual precinct body preflight and coefficient execution

The actual `decode_precinct_packet` body-range and coefficient-execution loops
now run through `preflight_packet_body_ranges` and
`execute_packet_body_contributions`. They are moved production loops, not
duplicate executors. Both have unconditional complete Result/state relations
over the caller's actual optional descriptor slice, raw progress, body bytes,
decoder slice, execution flag, error offset and real owner caps.

`part1_packet_body_preflight` retains the checked end before a truncation error
and does not advance its index on that error. `part1_packet_body_execute` includes
every decoder and all local counters. The actual per-block mixed transaction
commits before segment accounting, which precedes pass accounting and offset/
index advancement. Late failures preserve exactly those earlier effects.
Skipped execution still validates and consumes byte ranges; it need not have
matching decoder storage and preserves every decoder and decoded counter.

The logical descriptor sequence delegates F5L's sole optional contribution view.
The actual mutable slice borrow is closed before proving the complete nested
decoder-vector frame. There are no header-validity, shape, success, adequate
budget, supplied decoder outcome or supplied expected trace premises.
Independent literal-byte tests exercise skipped malformed storage, full native
cursor domains, truncation/address priority, prior coefficients and both late
counter-overflow positions.

These close the actual body-loop substage only. The enclosing precinct caller
still must derive the descriptors and reader/tree/state effects from the real
header producer. No complete header, precinct, progression or F5H theorem is
inferred from this intermediate result.

### Actual precinct header association traversal

`decode_precinct_contribution_headers`, its real member loop and its real slot
operation now compose the complete native header producer directly. Their
unconditional relations retain all packet-state entries, all subband metadata
and both complete raw trees per subband, the full optional descriptor sequence,
reader state and all traversal/count fields. No header outcome is supplied.

Geometry, physical storage, context/layer/style and checked address failures
precede each actual header operation. Native style comparison deliberately
ignores the force-selection bit; its exact historical policy is preserved.
Mutable packet-state and tree borrows are scoped only around the actual header
call, with explicit nested-vector and selected-subband metadata frames.
Count overflow occurs after the actual header commits, before descriptor-slot
lookup/storage; local and subband index advancement follow in order.

Independent literal `c2` and `c3 00` headers exercise normal association,
overlapping raw subband ranges (two counted contributions overwriting one
slot), unused second-subband trees, late count overflow and missing descriptor
storage after real reader/tree/packet-state effects. These cases are not
excluded by normalized geometry, storage, header or budget premises.

Those stages alone close header association and body loops. The following join
additionally closes the complete single-packet `TilePartPayload` precinct caller;
progression and reassembly remain separate.

### Complete actual single-precinct packet caller

The original `decode_precinct_packet` unconditionally refines
`part1_precinct_packet`, with its actual `TilePartPayload`, bytes, offsets,
expected SOP sequence/packet length, execution selector and typed owner caps.
The post relates the complete native Result and all precinct identity, contexts,
packet states, raw subbands/trees and entire decoder states. There are no
shape, valid-style/header, successful-decode, adequate-budget or trace premises.

The real component-style lookup and Tier1 byte parser now supply their owner
results directly. Exact owner SOP/EPH observations and packed source presence
select the real path; neither a style result nor a header result is supplied.
The `5972cc2` owner limit views are consumed through the actual getters and
typed packet-reader factory, including original code-block/work cap priority.

Marker/prefix admission, header association, and post-header execution are
actual production phases, not executable proof copies. Their separation keeps
the complete proofs within unchanged default limits. Explicit equivalent
matches expose real first-error branches rather than relying on unspecified
higher-order error closures. Prior failed monolithic proof attempts remain
private evidence; no proof limit, arithmetic domain or primary pin is changed.

Complete SOP sequence and packed-range ordering precede the actual prefix
reader and packet-present bit. Actual descriptors are allocated and produced
through F5L's sole reader/tree/header algorithms. Alignment and EPH precede
whole-body preflight; actual mixed body execution then precedes final logical
length and numeric conversion checks. Packed and inline physical offsets remain
distinct. This precinct operation is deliberately not globally transactional:
early header/tree effects and later decoder commits survive appropriate errors.

Independent literal marker/MQ/HT fixtures cover packed/inline accounting, skipped
execution, actual nonzero HT output, malformed/truncated markers, shape/cap/
offset/component priority and late length mismatch after decoder effects.
Proved properties preserve readonly identity/contexts, first-error priority,
preflight-before-coefficients and every prior state effect at final accounting.
This is not progression, tile-part/header reassembly, packet-length iteration,
JPIP outer-transaction or whole-F5H completion.
## Exact retained HT and selected group acceptance

Four finite result/model/complete-state/input recipes bind the actual retained
refinement, placeholder step, repeated placeholder loop and staged group
producers. Mutations reject unrelated returns/models, old or partial final
states, wrong actual inputs/pass counts/caps, extra unbound mutable state and
incorrect owners/callers. A later correct clause cannot mask the primary
whole-result clause's wrong argument binding. Trait Clone is proved data
support, not a request for generic trait or implication matching.

The legacy three-pass refactor's actual direct bypass caller is
`RawBitReader::decode` in `impl Tier1SymbolDecoder for RawBitReader`, not the
trait declaration or an older direct-pass wrapper. The curated raw-reader
entry names that real edge. Only this exact known trait/owner method has
additional formatted-scope resolution; unknown traits, foreign owners, nested
functions and ambiguous inherent/trait duplicates reject. A trait name before
`for` is not misidentified as the implementation's receiver type. No runtime
adapter or decoder body is added to satisfy the inventory.

The relation above covers this caller boundary. Complete mixed packet-body
acceptance is described below; neither boundary by itself establishes a raw
codestream-to-frame theorem. Exact-candidate qualification remains separate.

## Complete actual mixed packet-body acceptance

The actual staged body and outer whole-decoder clone/commit body now have
unconditional complete native Result/state relations. They execute the shared
preparation once, then the real HT or legacy loop, with exact body slices,
all164 stored segment entries, ordered counters/caps and public rollback.
Both earlier selected-route results remain consequences, not entry premises.

Ten finite exact producer/model/state/input recipes cover the shared header
segment accessor, preparation, both real helper families and the mixed
staged/public body. Aggregate legacy progress binds every mutable decoder,
index, offset and pass field; HT progress and separate counters likewise stay
complete. Negative tests reject partial or success-only states, unrelated
inputs/models, wrong caps, omitted mutable state and a bad primary binding
hidden by a later correct clause. Real production callers are required.

The standalone public Tier1 segment dispatcher is also proved unconditionally,
but is listed as proved API support rather than inventing an internal caller
for the curated inventory. No generic expression/implication matching or
mutable-completeness policy is weakened. Actual header/TagTree and precinct
composition remain separate F5L/F5H obligations.

## Complete native container, selection and typed-output composition

The actual native `ImageSize` tile count/bounds, selection construction and
`validate_selection` now refine full value/error models. The production path
checks origin overflow, physical grid/count admission, explicit empty/range/
duplicate/rectangle rules, region bounds and every intersecting tile in its
original order. Raw geometry and request contradictions are not normalized.
Private rectangle bounds are derived from the executed public checks and
native u16 coordinates, not public shape premises.

The actual requested-selection coordinator composes this result with reduced
target coordinates and sampling/registration context. All four targets are
modeled by their complete sequence values, not opaque array identity. Logical
component counts need not fit the physical64 entries; zero subsampling,
discard>=32, saturated context and unaccessed malformed fields retain actual
behavior. The original public selection APIs share one real constructor body.

The actual selected-codestream header producer chooses the parsed association
or real fallback and reports a missing association at its real box offset.
Actual container/codestream metadata validation includes native uniform/
variable bit-depth behavior without invented precision/sign checks. The real
associated-output stages compose CMAP/palette/CDEF/image admission with full
and selected color conversion. The selected finishing body composes mapping,
color and crop, including None bypass/missing-header ordering and actual byte/
work admission before later crop errors.

Twenty-two finite exact producer/model/result/input recipes bind these actual
stages and genuine callers. Independent tests compare27,648 raw geometry/
request/context cases,1,536 uniform-header cases, actual header choices and
offsets, known full/selected grayscale samples, None identity, malformed typed
state and first budget errors. Earlier component/color/crop oracles remain.
This closes the selected F7 computational boundary relative to native parsed
metadata and typed components. Compressed parser-to-pixel/frame composition is
F8, not a supplied decoded outcome assumed by these producers. Independent
normative endorsement, official vectors and full publication remain separate.
Conservative tests, both whole roots and all frozen/hosted gates must still
qualify the exact delivery before it is counted integrated.

## Conservative complete header and precinct acceptance

Thirty-nine finite owner-qualified producer/model/result/input recipes bind
the actual reader/raw-tree/header, byte-style and scalar-admission producers,
all three real slot/member/subband association traversals, and the four actual
single-precinct prefix/header/body/accounting callers. Heterogeneous whole
result tuples have explicit finite projection/state patterns, not a general
expression or implication matcher. Every actual mutable parameter must occur
in the complete final tuple; primary old-input/cap matching is anchored at the
same full-result model occurrence. Complete native producers reject newly
inserted validity/success/budget preconditions.

Owner observations, alignment, static APIs and raw-tree clone support remain
whole-root-proved support rather than invented independent result consumers.
Tests mutate every registered result/model/native input/cap/state/old-final
projection, guarded post and fabricated caller, including later correct clauses
that must not mask a wrong primary relation. The conservative index is still a
curated technical reference inventory, not exhaustive normative conformance.
Full progression, packed reassembly, length iteration, JPIP transaction and
whole F5L/F5H closure remain separate from this actual single-precinct stage.

### Actual raw packet and progression iterators

`packet_progression.rs` and the actual `PacketGrid` lookup/selected-count
methods admit all nine stored grid fields, including inconsistent physical
arrays, totals and offsets. Actual `unravel`, candidate decoding, packet
iteration, POC candidate counts and offset decoding have complete typed results.
Inverted component spans deliberately have different count/decode behavior.

Both actual iterator constructors share one verified production free factory
with their preserved public static wrappers. The complete packet iterator
relation retains grid/order and both counters. The complete progression
relation additionally observes every raw POC record, all three window cursors,
outer emission and the entire optional nested default iterator. Default errors
retain nested cursor/emission changes without synchronizing outer emission.
POC errors retain candidate advancement, late emission rejection and ordered
window advancement before a failing next-window count.

Actual prior-window membership, one candidate step and window advancement are
production phases, not proof-only decoder copies or supplied coordinate traces.
Native fixtures cover physical lookup boundaries, skipped candidates, saturated
counts, duplicate-window work charging/suppression and exact late-error frames.

The actual component/selected grid factories now additionally refine
`part1_packet_grid_new`, observing all nine returned fields and every error.
Their sole executable body derives the maximum resolution, complete raw
count/offset summary and selected count through real production phases, then
performs the actual typed cap/product checks in order. Native offsets, full
stored packet totals and candidate work are not replaced by selected totals.
Public static wrappers preserve their API and share this verified free
implementation; internal proof callers use the actual free API rather than an
unsupported static-`Self` specification binding. Parent's actual typed limit
getters provide the caps. No successful factory outcome or normalized input
shape is supplied.

### Complete actual multi-tile-part progression caller

The actual selected `decode_progression_tile_packets_selected` and public
`decode_progression_tile_packets` now have unconditional Result/full-precinct-
vector relations to `part1_progression_tile_decode`. Inputs are the actual raw
`TilePartPayload` sequence, complete raw grid, complete initial precincts,
actual optional resolution counts and real `ResourceLimits`. There is no
supplied coordinate sequence, reassembled-byte/length bank, header/decoder
outcome, valid-shape, normalized-metadata, success or adequate-budget premise.

Real production preparation composes component-style lookup, typed tile-part
caps, selection admission, F5L's sole actual packed-byte reassembly, raw length
metadata and complete precinct-grid association. It preserves per-part and
aggregate checks and ignores no contradictory native source/count fields.
Actual packet/progression factories and `next_packet` produce coordinates;
actual `PacketLengthIter` initialization/advancement produces expected lengths.
Neither is replaced by a caller-supplied list.

The real progress record observes both full iterators, tile-part and length
owners, both byte offsets, every packet/statistic counter, the complete seen
vector and remaining work. The iterator advances before the real work guard.
Tile-part transitions can discard that coordinate, reset to the next part's
actual POC/default order and then suppress duplicates. Length consumption still
precedes seen checks. Complete context-layer writes precede selection/packed
lookup and actual single-precinct decoding; scoped native borrows frame every
untouched precinct and every nested owner.

Ordered accounting preserves the new tile offset on later packed-offset error,
packet-count commit before seen storage, and seen storage before later statistic
overflows. Its ordinary input is the actual returned packet decode, bound by the
complete producer relation. An explicit equivalent Boolean-to-word expression
exposes the real 0/1 value rather than assuming a missing standard-library
conversion specification. The boundary scanner separately proves its entire
state and unchanged-owner frame; those fields are not postulated unchanged.
Trailing data, excess/truncated lengths, missing packets and final conversions
retain original error order and all earlier precinct/coefficient effects.

Independent full API fixtures include literal nonzero HT cleanup, selected
higher-resolution body consumption without coefficient execution, tile-part
iterator restart/duplicate effects, late trailing data after real coefficients,
actual PPT reassembly plus PLT iteration with zero physical tile-body bytes,
and exact work/ordered-overflow states. These are not model-generated expected
outputs. This closes the named actual progression producer scope, not every
single/multi-code-block or JPIP outer wrapper, normative endorsement, the whole
F5H epic or project completion.

### Complete actual public packet and JPIP boundaries

The original `decode_single_code_block_packet` and
`decode_multi_code_block_packet` now have unconditional complete Result and
whole packet-state/tree/decoder relations to `packet_boundaries.rs`.
`PacketCodeBlockExecution`'s actual mutable bundle fields appear in the public
multi post; no separate successful execution object is supplied.

Single uses the real validated whole-payload factory, exact absent-packet
trailing-data policy and real header producer before actual mixed body
transaction. Later body failure can retain earlier header/tree commits.
Multi retains its raw shared-tree admission and complete context validation,
native SOP policy (including deliberately unchecked sequence values), exact
EPH placement, real descriptor generation and whole-body preflight before
any coefficient execution. Its result reports a prefix, not assumed complete
tile-part consumption.

Both real body paths now share one executable preflight and one executable
contribution loop. Explicit truncation/local-error offsets preserve the
historical precinct-zero versus multi-caller-offset distinction; actual
decoder-origin errors retain their own source offsets. Existing zero-offset
models remain exact proved specializations of the shared raw relations.
Full entry-expression and nested-vector frames, not stronger input domains
or raised limits, establish every first-error partial state.

The actual `decode_jpip_precinct_packet_inner` composes real context-layer
writes, original inline metadata construction, the actual absent source
constructor and actual skipped-body precinct decode. Its result and complete
state hold for malformed contexts/trees/decoder state and arbitrary bytes/caps.
Unobserved cloned template metadata is not treated as a supplied decoder or
clone result. Relevant readonly fields come from actual native copies;
`85697b6` exposes only the real packed-none constructor observation.

The actual subband Clone copies every scalar and faithfully clones both
complete raw trees in original order, retaining unused nodes and levels.
The original outer Vec clones/restores prove exact state/context/subband
snapshots. Decoder and identity preservation follow from the actual skipped
execution path, separately proved through the production bodies. Thus the
original outer JPIP transaction has a complete Result/whole-precinct relation
and full rollback on every error, not an assumed clone or frame-only claim.

Independent fixtures cover single cap/trailing/no-contribution/body errors and
nonzero HT output; multi late shared-header/count/storage and prior-decoder
effects, real local-versus-child offsets and sequence/prefix policies; actual
JPIP raw rollback and inline decoding despite genuine template PPT/PLT metadata.
This closes the four named original packet boundary guarantees. It does not
claim an entire image/parser theorem, human normative endorsement or automatic
epic/project completion.

## Conservative complete progression and raw input acceptance

The exact native progression/input registry admits only42 finite qualified
result/model/full-state/input shapes: the real packed reassembly/length
producers, grid factories/lookups, both nested iterators and the actual
multi-tile-part preparation/boundary/context/precinct/accounting/run/finish
chain. Forty have genuine internal callers and are curated as functional
contract links. The public selected-count and unselected delegation APIs
remain proved API support rather than invented internal consumers.

The real iterator factory and full context-layer update use explicit complete
semantic functions equivalent to their original literal/map posts; native
execution bodies are unchanged. Every mutable parameter must occur in the
complete final relation, and every real old input/selection/cursor/cap binds
the primary model clause. New premises, guarded or partial state, wrong
constants/views/inputs/caps and later correct clauses masking a wrong primary
are rejected. A producer cannot name itself as its own claimed consumer,
including a same-spelled call to a different receiver type.

The existing header/precinct families remain intact. Full raw source/owner
observations and static None APIs are supported without claiming separately
bound constructor results that the pinned frontend cannot express. This
remains a curated technical inventory, not exhaustive normative coverage.
The separate public code-block/JPIP wrapper guarantees are described below;
whole F5L/F5H delivery acceptance remains separate. No F8 image/parser or
general MCT claim follows from these progression references.

## Complete original packet and JPIP boundary guarantees

The original single-block, multi-block, JPIP inner and JPIP transaction entries
now have complete unconditional native Result/state contracts. Actual faithful
subband/raw-tree cloning and the original Vec snapshots/restores establish
whole rollback; skipped execution preserves real decoders and readonly
identity without a supplied clone or decoder result. Multi-block execution
shares the actual preflight/body loops with exact truncation/local error
offset policy; genuine child decoder errors are not remapped.

Fourteen finite exact boundary shapes retain every result/view/old-input/cap/
error-policy argument. The two standalone public single/multi APIs remain
proof-supported APIs, not fictional internal consumers; their full contracts
are additionally checked through an explicit two-key proof-support whitelist.
All functional contract references still require a distinct real consumer.
No generic root/expression/implication fallback is added.

The native execution bundle is recognized only for its exact existing type,
parameter and four named mutable fields. The complete final tuple must cover
all of them; adding a mutable field, changing the readonly context slice or
using an unknown bundle type fails closed. Negative tests include all dotted
old/final fields, later correct clauses masking wrong primary inputs, exact
offset policy and all public API/consumer distinctions. The only private
reader cleanup removes the now-unused three-line `new_prefix` delegate and its
redundant assertion; the actual free/public reader and full-state tests remain.
No full image/parser, general MCT, official conformance or owner-main acceptance
is implied by these boundary proofs.

The unchanged HT segment body uses a fresh solver context (`spinoff_prover`)
to avoid accumulated whole-root solver-state sensitivity after composition.
Its complete Result/state relation, native body and resource budget are unchanged.

## Reproduce verification

The [Verus workflow](.github/workflows/verus.yml) pins the verifier archive,
checksum, required Rust toolchain, and command. Use the same versions when
reproducing it locally. Do not substitute a rolling compiler without
revalidating the source and standard-library specifications.

The pinned release includes `cargo-verus` beside `verus`; put that directory
on `PATH`. Use its required Rust toolchain (`1.98.1` for the pinned release),
separately from the ordinary decoder toolchain. The root manifest opts the
same production crate into verification.

The `verus` Cargo feature supplies the exact pinned `vstd` dependency.
It is deliberately not a default feature: ordinary decoder builds retain an
empty dependency graph. The frontend does not enable optional features
automatically, so include `--features verus`. The released lifetime boundary
below still requires `--no-lifetime`; it is not hidden by a wrapper script.

From the repository root:

```sh
RUSTUP_TOOLCHAIN=1.98.1-x86_64-unknown-linux-gnu \
  cargo verus verify --features verus --locked --fwd-verus-args-to roots -- \
  --no-lifetime
```

To collect the same whole-crate evidence as CI:

```sh
mkdir -p target/validation
RUSTUP_TOOLCHAIN=1.98.1-x86_64-unknown-linux-gnu \
  cargo verus verify --features verus --locked --fwd-verus-args-to roots \
  --target-dir target/verus --lib -- --no-lifetime --output-json \
  > target/validation/cargo-verus-output.log
python3 validation/generate-proof-coverage.py \
  target/validation/cargo-verus-output.log
```

The collector extracts exactly one root result, writes normalized
`verus-result.json` and schema-v3 `proof-coverage.json`, and binds both the raw
Cargo output and normalized result by hash. The expected crate namespace is
`jpeg2000_rs`, not the standalone compiler's default `lib`.

The report's `results.source_function_coverage: "not-measured"` is informational:
the collector does not compare a complete source-function inventory, so there
is no measured denominator or coverage percentage. Observed verified project
functions, verified obligations, zero Verus errors and documented Rust-only
adapters remain separate fields; observed functions are not thereby claimed
to have end-to-end contracts. This status never substitutes for successful
whole-crate verification. Historical schema-v2 reports, including their former
`incomplete_production_functions: 0` field, describe observed results, not an
exhaustive source-coverage measurement. Retain historical evidence unchanged;
regenerate with the commands above to produce a report for the current schema.

Cargo can reuse an already verified artifact without emitting fresh JSON.
For a fresh local report, clean only this crate's verification artifacts with
`cargo clean -p jpeg2000_rs --target-dir target/verus`, then repeat the report
command. CI uses a fresh checkout. Reports are generated evidence, not
committed snapshots; an empty/cached output cannot become a new proof report.
If Cargo refuses to clean because the target lacks a valid `CACHEDIR.TAG`,
respect that safety check. Use a new dedicated `--target-dir` for fresh
verification instead of deleting the unrecognized directory.

The checker rejects missing/zero/dependency-only/wrong-crate/ambiguous/partial
results, any termination opt-out, and forbidden trusted codec escapes.
Cargo's exit code alone is not proof evidence. Keep this gate enabled.

For module debugging, the pinned frontend requires `focus`:

```sh
RUSTUP_TOOLCHAIN=1.98.1-x86_64-unknown-linux-gnu \
  cargo verus focus --features verus --locked --fwd-verus-args-to roots -- \
  --no-lifetime --verify-module refinement
```

Module-only results are not accepted by the whole-crate collector. CI
explicitly exercises that rejection before its complete verification.

Reuse a dedicated scratch target for iterative debugging rather than rebuilding
the verifier dependencies into a new target for every edit. Batch related
functions in one focus run to share whole-crate Rust/VIR frontend work. For
one function, use `--verify-only-module image --verify-function function_name`;
`--time --output-json` separates frontend and solver costs. Check that the
intended function actually ran and produced nonzero verification results.
These scratch results remain debugging evidence only: final acceptance still
requires a fresh complete production-root run and the fail-closed collector.
Keep raw proof reports separate from disposable compiled scratch profiles.

## Current lifetime-analysis limitation

The pinned released verifier requires `--no-lifetime` for verified-module
constant initialization because of an upstream THIR/erasure initialization
error. The proposed upstream fix is
[verus-lang/verus#3266](https://github.com/verus-lang/verus/pull/3266).

This flag disables Verus lifetime analysis, not Rust borrow checking.
Documentation must not imply that lifetime analysis ran. Remove the flag
only after a reproducibly pinned fixed verifier passes the exact production
root and the relevant upstream regression suites.

## What the proofs establish

### Full native magnitude arithmetic

`magnitude_value` is the closed natural-value projection of all six
little-endian limbs. Native `checked_add`, `checked_shl`, `shift_right`,
`low_u64` and `is_zero` refine exact sum/capacity, multiplication/floor
division by powers of two, modulo-low-word and full-value zero semantics.
All `u16` shift values are covered, including large-shift zero success and
nonzero overflow. No coefficient-normalization or HT-success premise is
assumed. Public associated factories retain their API while verified free
factories supply complete producer contracts, including exact invalid-bit
errors and identity with `Magnitude::ZERO`.

The existing limb implementations are related to natural arithmetic through
proved one-bit word composition, full-value carry identities and capacity
bounds, without raising verifier limits. This interface supports actual
HT reconstruction but does not by itself prove HT byte meaning or F6's
remaining assembly bridge.

The unchanged native `Magnitude::limb` also has an exact full-`usize`
`Option` contract: each index below six returns its corresponding raw word,
and every other index returns `None`. The pure owner representation proof
`magnitude::representation_proofs::magnitude_limbs_shape` exports the intrinsic
six-word shape without exposing private fields or requiring an executable
getter call. A separate property in `proofs/spec_properties` checks that this
closed-view interface is usable from another module. These are raw
representation facts, not additional Tier-1 coefficient meaning.

`Magnitude::checked_sub` has a complete no-requires full-native Result
contract: exact 384-bit natural difference when ordered, exact arithmetic
underflow otherwise, including equal operands returning zero and full raw
representation/value/shape/capacity binding. The optimized executable
subtraction is unchanged. Its comparison guard is linked to natural prefix
order, and the existing carry-prefix algebra is reused for borrow propagation,
including incoming borrow with an all-ones subtrahend word. Independent bit
borrow tests compare complete results across sparse, boundary and dense pairs.

### Bounded supplied-coefficient reconstruction

`transform::inverse_quantize_values` and `transform::inverse_quantize_plane`
are the real production cores shared by the public integer and internal
signed-magnitude adapters. Their complete-result contracts relate every sample
and all `ReconstructedPlane` metadata to
`part1_inverse_integer_quantization` / `part1_inverse_quantization`, including
parameter, explicit decoded-byte-budget, ROI, arithmetic and final width
rejections in execution order. The domain includes all six-limb coefficients,
signs and `u8` ROI shifts; out-of-range restored magnitudes are rejected rather
than assumed absent. The original `inverse_quantize` and
`inverse_quantize_magnitudes` adapters also have complete Result contracts
using the closed `ResourceLimits` byte-field projection and its verified getter.

`transform::inverse_5_3` and `transform::inverse_9_7` have whole-sequence
contracts covering both parities, empty/singleton handling, mirrored boundaries,
all scaling/lifting passes and checked errors. The horizontal, vertical and
single-level 2D public entry points for both standard kernels additionally
specify every plane sample, all metadata and the actual configured byte limit.
The real level implementation reuses the proved production row/column
coordinators. `inverse_lift`, scaling, the four-stage 9/7 coordinator and column
storage specify complete mutable states on first failure, with untouched
positions retained. Supporting model properties establish complete sequence
lengths and plane sample-count/metadata consistency.

The existing public `convert_samples` API has full Result semantics for its
actual 1..38 precision policy, rounding, level shifting, clipping and checked
failures. Its concrete consumer is an independent API test, not the decoder's
separate image/component conversion path. Independent tests compare complete
outputs and error/mutation boundaries with bit-expanded ROI, rational Q16 and
widened-integer sequence/plane/conversion references.

The actual free `apply_reversible_component_transform` and
`apply_irreversible_component_transform` APIs have complete mutable-image
contracts, not just scalar arithmetic bounds. A closed `DecodedImage` view
contains every image/component metadata field and all sample buffers. The
shared real loop's ordered compatibility, length and arithmetic checks are
modeled together with complete failure states; metadata, lengths and every
extra component remain unchanged. Independent widened-integer tests compare
entire images, including earlier committed pixels on a later error.
No typed/CDEF structure or conversion is duplicated or modified.

Raw closed arbitrary-kernel/step/coefficient views and exact receiver getter
contracts make their consumed representation available without validation or
coefficient-normalization assumptions. They are interfaces for further
arbitrary-kernel work, not a whole-kernel theorem.

The actual quantized-block placement loop in
`decode::prepare_tile_component_with_kernel` is a shared, verified production
block/row/pixel transition. Its complete working-subband view includes both
samples and visited flags with exact first-failure buffers, unchanged metadata
and lengths, monotone visited flags and protected previsited values. Independent
wide-index tests cover full grids, short buffers, overlaps, empty blocks and
coordinate failures. Geometry/quantization checks stay before the same real
call. This is the complete write stage, not a result theorem for its surrounding
placement or multilevel coordinator.

The actual `assemble_image` and active `assemble_selected_image` entry points
now have complete, unconditional Result relations over supplied tiles. Every
output sample, component-info field, dimension, origin and fraction value is
modeled. Shared actual component/tile/rectangle/row/pixel stages preserve complete
partial sample/mask states, with first-error absorption. Registered coordinates,
physical component-info bounds, cumulative decoded-byte charging, fraction
consistency, overlaps and missing coverage retain their native ordering.
Selected assembly keeps its distinct intersection-only sample domain and
selection coverage errors; off-region matching tiles still undergo fraction
and extent checks. Budget checks remain before crop-offset arithmetic.
Independent widened coordinate/image tests compare complete results and exact
error boundaries, including raw fractions and non-normalized metadata.

Raw component-info lookup and reconstruction direction/count selectors have
full-native-domain Result contracts with no valid-header or array-size premise.
The only deleted inactive implementation is the nested selected-assembly
duplicate; active production callers use the shared verified stages.

The existing decoder component/image typed conversions now have complete
Result relations using the actual F7 views, including all signed/unsigned
samples, image/component metadata and the existing empty channel definitions.
The original production loops retain their precision, per-component and
cumulative byte-budget order. Fraction validation happens per accessed sample,
so empty components with valid precision keep their native arbitrary-fraction
behavior. Rounding bias and unsigned level-shift overflow precede clipping;
no geometry, normalized-input or sufficient-budget premise is introduced.
Independent widened references cover every `u8` precision/fraction value,
complete sequences, whole images and exact error precedence.

The narrowly scoped read-only packet decoder accessors also expose their
actual private Vec through a public closed view, exact entire-`usize`
indexed reference Result, count and complete slice contracts. Parallel
packet-state/context shape and entropy meaning are not assumed.

These are input-relative integer/fixed-point stage results, not compressed
parsing/Tier-1 meaning or measured irreversible conformance.

The actual public `prepare_tile_component` now closes the complete standard
None-kernel plan coordinator: raw decoder/plane and six-limb coefficient reads,
signed midpoint handling, initialization and nine-byte cumulative charging,
ROI/quantization, placement/coverage/fraction checks, the entire mixed-direction
multilevel 5/3 or Q16 9/7 fold and every final PreparedTileComponent field/error.
Its original private with-kernel body shares these real stages; the complete
native None/Some extension below preserves the original None result.
All public native malformed-input and resource cases remain modeled rejection,
not header/normalization/coverage/budget/success/trace preconditions.
The prepared-to-tile getter also has exact full-field/sample semantics.
Independent full-plan and ordered-error tests use the previous widened
reference algorithms and completed one-bit input blocks, not subject transforms.

Seven exact inventory recipes bind those complete returned objects to their
actual plans, precincts, styles, planes, coordinates, fractions, selected counts,
detail indices and decoded-byte cap. Negative tests reject incorrect listed
models, unrelated or partial results, constant/reordered native inputs and
success-only substitutions. The standard entry does not claim the generalized
private producer under a standard-only model. No generic expression or
implication matcher was added.

### Complete native arbitrary kernels and None/Some preparation

The actual `inverse_arbitrary`, horizontal/vertical/2D arbitrary entry points
and their shared production stages now have complete unconditional native
Result relations. The raw kernel/step/coefficient views bind actual flags,
full bytes and vectors. Interleave errors and singleton truncating half precede
scaling; missing/zero scaling and every integer/binary32/binary64/binary128
coefficient conversion, reverse-step order, parity, sample extension, source
sum, checked wide arithmetic and exact final/partial buffers are included.
No valid descriptor, normalized shape/precision, successful lifting operation
or execution trace is a premise.

The Q32 model distinguishes native truncating division, ties-even binary
coefficient conversion, the existing excessive-right-shift zero cutoff, and
the signed lifting bias before arithmetic shifting. Explicit checked-result
matches, proved shift bounds and a faithful explicit zero/one rounding
increment expose the existing semantics without adding trust or proof limits.
The nonresizing lifting bodies use mutable slices and retain one executable
body, actual update order and late-error partial writes.

The actual `prepare_tile_component_with_kernel` now unconditionally equals
`part2_prepare_component`; the former standard models are exact None wrappers
of the same shared semantics. Every native style/kernel combination is
admitted: style selects quantization reversibility, a supplied kernel selects
the actual inverse operation, and the existing fraction mismatch rejects only
after that operation. Zero-resolution paths do not invent kernel validation.
The multilevel fold and every final field/error remain complete, including
the distinct nine-byte working sample/visited charge.

Native regressions cover all 256 kinds, four physical-width hints and all
flag/parity/reversibility combinations in 32,768 contexts, independent
integer-rational Q32 rounding and binary-layout edges, exact exponent-127
rejection, reverse-step parity, ignored/unvisited defects, late partial writes
and real None/Some preparation/fraction/budget error order. Twenty-one finite
exact producer/model/result/input recipes bind every newly claimed scalar,
sequence, plane, partial buffer and preparation stage. Negative tests reject
wrong native views/flags/counts/caps, partial or success-only results and a
wrong primary clause followed by a correct duplicate. Whole-production
verification and targeted inventory tests pass; complete frozen numerical,
resource and hosted qualification remain separate acceptance gates.

### Complete native MCT arithmetic and matrix-row boundary

The actual MCT rounding/rescaling, optional integer/scaled offsets, scratch
admission and nontransactional work charging now have complete native
result/state relations. Raw array owner views and exact getters preserve all
stored metadata/values. The owner proves the crate-private Q32 constant's value;
clients consume that fact without revealing private representation or raising
proof budgets. Equal source/destination precision bypasses later shift checks,
including native precision255, exactly as the body does.

The actual reversible and per-source-fraction matrix-row loops refine one
shared declarative dot fold. Coefficient indexing, native row multiplication,
precision/offset admission, every checked wide term/sum and final narrowing
are ordered exactly; empty rows and malformed physical arrays are not
normalized. Full matrix/offset/source/fraction/row inputs are bound, not
successful-row or rectangular-matrix premises.

Whole-production verification and strict Clippy pass. Independent arithmetic
tests cover all65,536 source/destination precision pairs, full-u8 rounding and
offset domains, native extrema, work counter partial errors and raw matrix-row
precision/index/error frontiers. This is a local arithmetic/row milestone,
not complete collection, dependency, wavelet, stage or general MCT execution,
external array-MCT qualification or whole F6 completion.

These arithmetic/row contracts alone do not establish collection or stage
composition. The [complete native MCT composition](#complete-wavelet-stage-and-real-owner-buffer-mct-composition)
section describes those additional actual producers. A whole-decoder,
raw-input-to-component-sample relation is a separate boundary; tile-sample
assembly alone does not establish it.
See the [reconstruction model reading path](specs/README.md#reconstruction-reading-path).

### General scope

Verification checks the properties expressed by contracts and loop invariants,
including bounds, arithmetic checks, termination, and selected functional
relations to specification helpers. The technical inventory
[normative-coverage.json](validation/normative-coverage.json) links implementation,
contract, specification, proof, and test symbols.

That inventory is not an exhaustive normative-clause checklist. A helper
contract is only as strong as its model and its relationship to the production
state/output. Review those relationships independently; symbol links and
successful obligation counts alone do not prove full standards conformance.

### Concrete contract boundaries

Read each contract according to its inputs and postcondition:

| Contract family | Established relation | Not established by that relation alone |
|---|---|---|
| Stream and packet accounting | Consumed offsets, declared lengths, ordering and bounded claims | That accepted syntax has the intended pixel meaning in every standard edition |
| Scalar refinement helpers | The implemented bounded arithmetic/bit operation agrees with its listed model | That callers chose the normative context, stencil, scale or traversal order |
| JPX source-over arithmetic | Exact natural-valued numerators and rounded scalar color/alpha results, proved in the 16-bit range at production conversion sites, with upward ties and transparent zero | Layer ordering, placement, sampling, persistence, or a complete composed-image theorem |
| Complete finite-channel pixel evaluation | One total model for all active colors and alpha, preserved unused slots, and exact invalid-input rejection for up to three normalized color channels | A complete theorem for planar gather/scatter, canvas traversal, layer order or whole-render transactionality |
| JPX planar pixel gathers | The complete optional pair of stack pixels, alpha values and representation flag equals the model of the actual source/destination planes and indices, including grayscale expansion, absent source alpha and all missing-sample rejection cases | That earlier channel-map resolution is normative, or that subsequent scatter, canvas traversal or layer/frame composition is completely correct |
| JPX planar scatter | Exact status and complete final color/alpha sequences, including the successfully written color prefix on a failed raw scatter, preserved other samples and plane lengths | That an arbitrary caller prevalidated every destination, or that an entire render is transactional |
| Complete normalized planar pixel transition | The actual gather/evaluate/scatter status and entire final planar state equal one composed model; rejected pixel inputs leave both color and alpha state unchanged | Earlier channel normalization, complete canvas traversal, work-limit transactionality, layer/frame order or a parser-to-pixel theorem |
| Successful placed-layer composition | On success, the complete final planar canvas state and exact work count equal a raster-prefix fold of normalized pixel transitions at the selected clipped, floor-scaled crop addresses | Complete error-state semantics, sufficient-budget success, earlier channel normalization, layer/frame ordering or a parser-to-pixel theorem |
| All-return placed-layer prefix safety | On every return, all buffers equal a valid raster prefix, and work accounts for that prefix or all but its final stored pixel; inactive geometry leaves the complete initial state unchanged | Which prefix must fail, exact error classification, sufficient-budget success, normalization or layer/frame ordering |
| Deterministic budgeted placed-layer execution | On every return, the exact typed `Result`, complete final buffers and work counter equal a raster fold that stops at the first checked-address, invalid-pixel, work-overflow or actual work-limit failure | Earlier channel normalization, layer/frame ordering, parser-to-pixel correctness or official conformance |
| Supplied normalized layer sequence | `render_decoded_layers` returns exactly `part2_render_layers`: global output-space choice, transparent canvas initialization, ordered cumulative byte checks, carried placed-layer buffers/work, first failure and complete final image metadata/samples | Which compressed layers/instructions are supplied, normalization/registration/opacity/chroma-key correctness, or complete frame/timeline orchestration |
| Supplied frame-table selection | `select_frame_instructions` returns exactly `part2_select_frame`: finite/indefinite modulo selection, exact selection errors, ordered persistent predecessors/current frame, and all instruction fields | Building the frame table, interpreting reuse, or a composed selected-frame-to-image theorem |
| Complete timeline construction | `build_timeline` returns exactly `part2_build_timeline`: repeated instruction sets, new/reused layer references, exhaustion, grouping/persistence, all frame/instruction metadata, checked timing and exact frame/work/arithmetic/conflict errors | Parsing life/tick fields or deriving the supplied composition metadata from compressed/container bytes |
| Complete supplied-layer frame composition | `render_normalized_frame` returns exactly `part2_render_normalized_frame`: actual selection, indexed normalized outcome lookup/consumption, first supplied-layer failure, then complete budgeted rendering and final image | Compressed decoding, earlier normalization/registration/opacity/chroma-key, or a parser-to-pixel theorem |
| Normalized image construction | `from_layer`/`from_composited` return exactly `part2_image_from_planes`: checked dimensions/plane cardinalities, exact errors, 16-bit precision, ordered channel kinds, whole-image alpha association and all buffers | The origin or correctness of supplied normalized samples |
| Complete converted-image layer construction | Exact typed result, dimensions, ordered color planes, optional sequentially combined alpha and representation flag for actual borrowed selection and owned copies | Earlier component/color conversion or association validation, registration/opacity/chroma-key, layer/frame ordering or a parser-to-pixel theorem |
| Complete typed JP2 color conversion | Every typed result, image field and color/alpha sample equals the composed model of the actual typed components, definitions, reference grid, color method and actual byte/work caps; includes complete preflight and fail-fast raster/channel traversal | Earlier compressed decoding, palette/container interpretation, selected-image crop or JPX registration/opacity/chroma-key; ICC methods are explicitly rejected, not executed |
| JPX destination stores | Exact success flag and final slice: the indexed sample is set to the requested value, all other samples and length are preserved; an invalid index leaves the slice unchanged | That the selected plane/index is the normative destination, or that an entire render is transactional |
| JPX placement coordinates | The selected floor-scaled source coordinates remain inside the cropped source, clipped destination coordinates remain inside the canvas, and actual read/write indices equal checked row-major addresses | Complete canvas traversal/channel routing, all resampling profiles, or an edition-level placement/conformance theorem |
| Tier-1 state and reconstruction | Selected pass-state, magnitude-prefix and integer-midpoint operations | A complete mathematical denotation of every code-block and inverse-transform combination |
| Complete raw-bypass reader transitions | Actual reader initialization, byte loading, bit result, every final field, exact input/work/overflow errors and predictable-termination result | Complete MQ decoding, packet/segment accounting, significance/refinement/cleanup traversal, coefficient meaning or end-to-end legacy correctness |
| HT directional reader/substream state | All five actual readers: exact constructors, bytes/bits/positions, MagSgn words and drain, zero/one fill, stuffing, exhaustion, full cursors/counters, shared cleanup byte claims and refinement physical-bit vectors/padding, exact inner/outer budget and overflow effects | Upstream partition/pass accounting, UVLC/quad interpretation, coefficient/block reconstruction, replacement/placeholders, mixed sequencing or complete F5H acceptance |
| HT cleanup multi-bit/event operations | Every `u8` VLC peek/advance count, non-mutating copied-reader peek truncation, fail-fast actual advance, complete MEL event cache/head/suffix/adaptation and full-width event-counter failure state | That callers request the normative symbols, select the right table/context, reconstruct full cleanup blocks or route mixed pass groups correctly |
| HT UVLC/quad-word interpretation | Actual prefix, all native suffix lengths, prefix value, initial/non-initial U pairs and quad words, with exact typed result and complete final reader/event/claim/work state; actual table selection, context-zero MEL suppression, length validation, advance and tick order | Normative codebook endorsement, context selection by the quad traversal, complete metadata/coefficient blocks, placeholders/replacement or mixed sequencing |
| Actual packet-pass placeholder grouping | Every native packet-pass input: exact typed rejection outside 1..=164 and all four cleanup/refinement/placeholder/skipped-plane fields inside it | Actual pass execution/replacement, segment partitioning, coefficient planes or mixed dispatch |
| Complete actual HT cleanup metadata traversal | Exact public/segment result for all native header values and actual byte/work limits, ordered row/pair/member quads, north/west/east contexts, suppression/UVLC/events, sample bounds/counts, collision, work/counter first errors and every metadata field | Numerical magnitude/sign/exponent or coefficient-plane reconstruction, refinement passes, placeholder/replacement execution, mixed sequencing or full F5H |
| Complete actual HT numeric MagSgn reconstruction | Every native parameter/flag and initial reader state: exact full 384-bit numeric magnitude, sign, exponent, typed first error and all final reader fields; actual full-value arithmetic through F6 contracts | Plane placement, raw high-limb storage, exponent stencils, final plane padding/termination, refinement or mixed sequencing |
| Complete actual HT cleanup-plane reconstruction | Every raw output coefficient and all six words/flags, actual constructor and metadata rejection, coordinate-overflow-before-clipping, ordered numeric consumption/placement/counters, both full exponent stencils/reset/swap and final physical padding/stuffing/work termination; no valid-metadata, matching-shape or numeric-success premise | Refinement passes, replacement/placeholder/mixed sequencing, a composed metadata-plus-plane decoder theorem or complete F5H |
| Earlier cleanup-only symbol stage, now subsumed | Actual metadata output feeds numerical reconstruction and complete duplication; decoder state and ordered accounting facts remain reusable native stages | This earlier stage alone did not establish supplied refinement or byte-input preflight; the complete entries below now do. Continuation/replay, placeholders/replacement/mixed sequencing and full F5H remain separate. |
| Complete actual HT significance/refinement plane | Both one/two-pass paths, all native header values and raw six-word states: actual reverse magnitude adjustment, stripe/neighborhood/causality, evolving discovery plane, per-patch delayed signs, every coefficient/flag/statistic, complete readers/claim/stuffing vectors and first-error/final-padding effects | Refinement continuation/replay, placeholder/replacement/mixed sequencing or full F5H |
| Complete substantive HT segment byte entry | Actual style/pass/set admission, real pass/byte/work caps, parser partitions, internal metadata-to-numeric-to-refinement composition, complete decoder state and exact ordered failures, including `None` versus `Some(empty)` | Separate refinement-contribution replay, placeholder skipping, replacement/multiple-group orchestration, mixed legacy dispatch, normative endorsement or whole-decoder/F5H completion |
| Complete retained HT refinement contribution | Actual retained-buffer clone/append and size/cumulative-byte admission, replay from the retained cleanup plane, native pass-group checks, empty-concatenation bypass, full output/data/control state and every transactional/late partial accounting error without normalized-state premises | Staged packet-group clone/commit orchestration, mixed legacy dispatch or full F5H |
| Complete native HT placeholder/replacement step | All native pass/phase/set states and real pass caps, exact cleanup-flag/buffer reset, preserved stored cleanup/output, multiple-set permission/counting and partial segment-overflow effects | Entire staged multiple-group/packet or mixed dispatch; no assumed Clone/legacy outcome is supplied |
| Actual selected HT staged packet group | Faithful whole-decoder raw cloning, original packet grouping, repeated skip-one/skip-two loop, substantive byte decode and whole-clone commit. Every failure preserves the complete original decoder; success reports the packet's original pass count. Includes raw malformed retained state and exact selected Mixed-with-cleanup-option route | Legacy dispatcher else, full mixed union, packet contribution/precinct orchestration or whole F5H; no supplied legacy/clone trace is accepted |
| Complete selected HT packet contribution body | Actual shared preparation, complete stored descriptors and physical bounds, real borrowed slices, cleanup/refinement/placeholder routing, complete decoder and local progress/error state, final totals and actual transactional whole-clone commit; no valid-header/state/success/budget premise | Header parsing, full legacy/HT union, precinct/packet orchestration, normative endorsement or whole F5H |
| Complete unconditional mixed contribution body and Tier-1 segment dispatch | Actual shared preparation, actual HT/legacy selector and complete native helpers, full staged errors, actual faithful clone/commit rollback and pass-zero/retained-cleanup-option Tier-1 routing; both selected relations retained without premises | Header parsing, retained packet associations, precinct/packet orchestration, normative endorsement or whole F5H |
| Raw Tier-1 producer interfaces | Actual decoder plane, raw dimensions/sequence/indexed result even for malformed shapes, full stored words/flags, exact legacy-midpoint signed magnitude and native arithmetic rejection; no normalized-coefficient premise | Entropy meaning, coefficient normalization, complete reconstruction coordinator or end-to-end pixel correctness |
| Decoded output shape | Nonempty image/component counts and rectangular sample cardinality | Pixel equality with the JPEG 2000 decoding process |
| Representation views | Mathematical descriptions used by the referenced lemmas | An automatic connection to all production state or end-to-end output |

The earlier cleanup-caller inventory retains three unconditional native stage
contracts: complete preparation, complete decoder store state and complete
plane duplication. Their exact result/model, old/final decoder view, actual
planes, counters and work-cap arguments are checked through the existing
conservative mechanisms. Negative tests reject unrelated, partial, reordered
or constant bindings. The actual symbol caller is now unconditional for both
absent and supplied refinement and is linked as a complete contract by the new
substantive-byte-entry profile, not falsely promoted from its old conditional
theorem. The pass-limit owner projection only specifies the existing getter;
its runtime body and policy are unchanged.

Twenty-seven finite exact result/model/view recipes bind all actual refinement
and byte-entry producers. Every mutable receiver or summary must appear as
complete final state, with the correct initial state, full-value magnitude,
coordinates/stripe/patch arguments, causal flags, pass/bitplane values and real
pass/byte/work caps. Refined statistics bind field three/count one, and merge
binds the complete actual other record. Input patterns are anchored to the
matched returned-result clause: a later correct occurrence of a model cannot
mask incorrect primary arguments. Actual duplicate-clause and first-only
mutation regressions cover that distinction. No generic expression/implication
matcher or mutable-state relaxation was introduced.

`normalize_component` has an unconditional complete result relation for
supplied typed integer components, target dimensions and reference-grid
origins. It covers every output sample, either signed/unsigned representation,
declared precision 1..38, fixed-point registration, subsampling, edge clamping
and the exact first typed error. Invalid precision, sampling, dimensions,
signedness tags, missing/out-of-range samples and checked coordinate/index
overflow are modeled rather than assumed away. Empty target height returns an
empty plane without sampling; zero target width is rejected first, preserving
the actual stage's behavior. This does not prove the earlier palette/channel/
container interpretation, full color-layout/sYCC/alpha pipeline or parser-to-
pixel relation. Public budget checking remains an earlier separate stage.

`channel_layout` now has a complete typed-result relation over the actual
ordered component/CDEF metadata. With no definitions it requires one component
per color and returns identity routing. Explicit definitions preserve ordered
alpha associations and flags, ignore unspecified channels, allow repeated
identical color assignments within one component, reject cross-component
conflicts, and check missing required colors only after the entire definition
scan. Invalid alpha-association errors therefore keep their actual precedence
over a later missing-color error. These contracts do not independently prove
that a container parser authored the normative definitions or close the
subsequent whole color/alpha conversion.

`normalized_at` and `normalized_difference_at` are connected to the actual
typed-image component sequence and origins, including component lookup and
all nominal sampling errors. Chroma differences subtract `2^(p-1)` and scale
by `65535/(2^p-1)`, rounding signed half ties away from zero. `sycc_to_srgb`
returns the exact separately rounded, clamped RGB triple for every native
`u16`/`i32` input, without a restricted-chroma precondition. The checked
`rounded_fixed` helper also retains both `i128` overflow boundaries. These
pixel results do not close the earlier component/output-budget validation or
the complete public color-converter channel/raster traversal.

The separate public `convert_jp2_color` contract now composes these relations
as `color_convert_jp2`. It has no valid-input, canonical-channel, restricted-
chroma or sufficient-budget precondition. Zero image dimensions precede
format selection; unsupported formats precede layout validation; layout
precedes component metadata; component metadata precedes output-byte/work
admission; and admission precedes every sample read. The complete sYCC raster,
ordered grayscale/RGB channels and all alpha channels retain their exact first
failure, including original association/premultiplication metadata. Output
dimensions, color space, precision and every sample are connected to that one
result model.

Component validation covers precision/tags, subsampling, registered spans,
dimensions and sample counts. Output admission retains native checked-count
overflow and exact `DecodedBytes`/`WorkUnits` limit/actual fields, with bytes
checked first. These are this stage's admission quantities, not a theorem
about global cumulative work or peak live allocation. The normalization
allocations retain ordinary Rust allocator behavior; allocation failure is
not invented as a typed decoding result.

The shared private channel/pixel helpers contain the original production
operations and are called by the real converter, not an alternate decoder.
The preflight invariant bundle is internal proof support under
`proofs/internal_specs.rs`; essential format, validation, traversal and error
semantics remain under `specs/`. Independent wide-integer tests compare 1,440
complete supplied-input images and metadata plus 180 native-domain admission
cases. Those direct typed-input tests are not new reference-qualified
compressed profiles. Palette/channel-map interpretation, container selection/
crop, earlier decoding and normative endorsement remain separate F7/F8/N1
obligations.

`ConvertedImage::crop` now has an unconditional complete image-result
relation to `color_crop_image`, including the actual selected-color caller.
Zero requested dimensions precede coordinate overflow, which precedes bounds
checking. The existing exact whole-image identity path returns the supplied
image without allocation or new plane validation; even an internally supplied
short plane is retained unchanged. Other rectangles copy only requested
samples, in channel/row/column order, with exact address and missing-sample
errors. Color space, precision, every channel kind and alpha association/
representation flag are preserved without a canonical-channel premise.

The private plane helper shares the original two-dimensional production
loops rather than replacing them with a slower division-per-pixel raster.
Its only rectangle-order premises are established by the real method's
checked geometry; no valid sample plane is assumed. Essential crop
denotations remain in `specs/`; the immutable preflight bundle alone is in
`proofs/internal_specs.rs`. Source-coordinate-mask tests cover 86,700 bounded
contexts, alongside explicit native-boundary and identity-bypass cases.
This proves cropping supplied converted pixels, not how the decoder chose
the requested region or produced those pixels.

The actual `convert_selected_color` caller now refines
`color_convert_selected` from supplied typed components, color method, target
rectangle and actual limits. It composes the real converter and crop
contracts instead of assuming an unconnected converted image. Format,
metadata, budget and sample errors precede target-coordinate subtraction;
invalid target subtraction retains the existing `InvalidCodeBlock` error,
while valid differences pass to the full crop semantics. Earlier compressed
decoding, palette/channel-map application and selection-target derivation are
not established by this typed-input composition theorem.

`layer_channels` and `owned_layer_from_image` refine `part2_layer_input`
and `part2_owned_layer_input` on every return, without assuming canonical
channel order or valid plane lengths. Their result projections include every
output field and preserve the exact error variant. Channel scanning precedes
area checking, required-color resolution and alpha validation. Red and gray
both select slot zero, and duplicate or out-of-range slots are rejected.
Alpha planes are combined in source order, rounding after **each** product;
one alpha retains its premultiplication flag, while multiple alphas produce
straight representation. Association metadata is already an input to earlier
conversion policy and is not revalidated by this stage.

The private constructor is a free function because the pinned `verus_spec`
attribute cannot infer an associated static method in this conditional-macro
layout. There is still one production implementation and no public API change.
The existing placed-layer theorem uses a fresh solver context
(`spinoff_prover`) to avoid accumulated solver-state sensitivity as the model
grows; its obligations and resource limit are not relaxed.

### F3 input-relative orchestration boundaries

The actual layer renderer now carries a deterministic sequence denotation
across every placement; no validity, budget sufficiency or trace assumption
is required. The render invariant includes every mutable buffer and both
counters; the byte-charge and placed-layer contracts cover **all** returns.
Byte charging precedes placement validation;
placed-layer stores/charges retain their existing error ordering. The final
image constructor is proved rather than treated as an unmodeled adapter.
The constructors are free functions for the same pinned attribute limitation
as the F1 owned-layer constructor; their bodies remain production code.

The internal renderer receives the byte cap explicitly. Each production
caller supplies `options.limits().maximum_decoded_bytes()`; the work cap is
still related directly to `ResourceLimits` by `resource_work_limit`.
This avoids adding an unproved/private-field limit accessor assumption or
changing the shared limits module. The theorem is relative to the supplied
byte cap and the actual work-limit view, not a proof of all caller code.

`build_timeline` now has an unconditional all-return contract, not merely
an instruction-step lemma. Its model starts from the actual empty state,
folds complete instruction sets and their repetitions, stops on layer
exhaustion, and absorbs the first error. The state includes the full pending
reuse schedule, next new-layer index, instruction position, frame table and
time. All instruction fields and frame indices/start/duration/persistence
are projected. The whole function proves its helpers' structural invariants
from initialization; that invariant-only predicate lives in
`proofs/internal_specs.rs`, not in the normative definitions. Helpers'
partially updated private state on error is not exposed by the result-only
timeline theorem. No successful frame state is abstracted away.

`render_normalized_frame` is the complete composition boundary. Its supplied
input is an **indexed outcome bank**, not an assumed execution trace: each
entry contains a layer reference and an optional normalized layer `Result`.
For each selected instruction, the actual collector consumes the first
remaining matching entry; arbitrary bank order, duplicate references,
unrelated entries, empty slots, errors and missing references are all modeled
without preconditions. Duplicate references consume successive outcomes
rather than silently caching one decoded layer. This is necessary to preserve
the existing per-placement decoder-call behavior. Missing references return
`InvalidBoxContents`; supplied failures retain their exact error variants.
All selected outcomes are gathered before rendering, so a later supplied
failure precedes an earlier layer's pixel/resource failure, as in production.
The actual complete selection and layer-render contracts establish the final
image, rather than assuming their outputs as trace inputs.

`render_inspected_frame` still decodes selected references in the previous
order, stopping at the first decoder error. It supplies those outcomes to
the proved normalized stage, which independently performs frame/reference
selection and propagates that first selected error before rendering. The
wrapper does not cache, skip or add compressed decoder calls. The extra
instruction selection is deterministic and has the same existing selection
errors; compressed decoding itself has no newly asserted denotation.

Independent tests compare 11,520 bounded timeline programs with a separate
flattened/BTreeMap scheduling and grouping model, including exact typed
errors. Frame tests cover every four-frame persistence mask, finite/indefinite
looping, extreme requests, indexed bank permutations and repeated references
with distinct normalized outcomes. Full multiframe images are compared with
wide-rational arithmetic, including metadata, alpha representation, complete
buffers, repeated-call determinism and loop reset. Dedicated cases establish
selection-before-supply and gather-before-render failure precedence.

These complete actual functions cover F3 relative to supplied composition
metadata and normalized layer results. They do **not** establish compressed
decoding, container-to-metadata interpretation, normalization, registration,
opacity or chroma-key semantics, nor standards-edition conformance. Owner
integration/review and package acceptance remain separate from these local
theorems. All complete output projections have exact inventory-scanner
mappings and linked `contract_refs`, including `build_timeline` and
`render_normalized_frame`.

The raw-bypass reader has unconditional exact typed result/state relations
for byte loading and bit reads, plus exact termination classification.
Its state model includes the immutable byte sequence, current byte, remaining
bits, consumed-byte index, marker-padding count and actual work counter/cap.
Stuffed data use seven bits; marker-like bytes beyond `0x8f` after `0xff`
remain unconsumed while synthetic `0xff` bits are supplied. Exhausted input
uses the same selected bounded-reader policy. These are input-relative
implementation semantics, not a completed selected-edition audit.

The frozen first F5H subprofile is documented in [specs/README.md](specs/README.md#frozen-f5h-directional-reader-stages).
It comprises `HtMelBitReader` and `HtReverseVlcReader` construction, loading,
single-bit reads, positions and counters, plus the actual shared cleanup
pair's constructor, `can_claim_byte`, `tick`, `read_mel_bit` and `read_vlc_bit`.
The three constructor bodies are shared private free implementations because
the pinned conditional attribute cannot infer associated static context.
The existing constructors remain thin Rust-tested adapters; no additional
executable decoder or trusted codec specification is introduced.

The mathematical transitions consume the actual input sequences. Their
postconditions specify the exact typed result **and every final field** on
both success and failure, without restricting the `u64` counter range.
VLC's terminal nibble starts at bit four; reverse stuffing excludes bit seven
only in the selected later-byte context. VLC charges the bit before eagerly
loading its predecessor, so the first rejected work charge leaves the old
byte and advanced cursor. MEL forces the low terminal nibble to ones before
testing its distinct stuffing rule. Invalid MEL stuffing leaves the entire
reader unchanged. Exhaustion and counter overflow retain their actual partial
state effects rather than being modeled as rollback.

The cleanup wrapper contracts compose those actual transitions, byte-claim
checks and outer accounting with complete nested-reader and MEL-event frames.
A collision precedes consumption; an inner failure does not record a claim or
charge outer work; an outer failure retains the consumed bit and recorded
claim. Mathematical prefix definitions and checked first-error absorption
lemmas describe fail-fast clients; they do not assert that callers retrying
after an error leave state unchanged. Independent fixed bytes and literal
expected bits/full cursors cover terminal stuffing, exhaustion, constructor
capacities, inner/outer budget order, collisions and full-width overflow.

The subsequent complete directional substages also cover the actual MagSgn
constructor, little-endian word loop, physical/fill/work counters and
bounded finish drain. The models include zero-count no-op, oversized-count
rejection, stuffed `0xff` synthetic fill, bad padding consumption and every
ordered overflow/budget effect. Finish checks the native `input.len() * 8`
fuel before testing pending physical data. Its semantic recurrence is not
an invariant-only witness and does not assume termination succeeds.

Both actual refinement readers have exact positioned and public bit-read
contracts. Their pair's full state includes both complete readers (including
an absent reverse reader), the entire claim vector and the entire stuffed-bit
vector. Reverse stuffed-bit recording precedes claim collision, so rejection
can retain both a consumed bit and a new stuffed mask. Work is the checked
sum of physical/fill counters after selected-counter charging. Padding finish
checks all encoded bytes without changing any state. A lexical mutable-borrow
scope and extensional vector frames make the existing claim mutation visible
to the verifier; the two public result projections use equivalent explicit
matches rather than a standard-library `Result::map` contract. No decoding
algorithm is duplicated or changed to suit an inventory expression.

The actual VLC peek/advance loops and MEL event machine refine semantic
recurrences for every native count/cache/counter input. Peek intentionally
returns a partial `u16` on copied-reader failure or result-width exhaustion,
without changing the real reader. Its loop distinguishes break-only results
from normal continuation. MEL cache priority precedes state validation;
event-counter overflow retains cache changes, and suffix-read failure retains
only actual nested reader/claim/work mutations. A literal maximum-exponent
fixture checks the five-bit MSB-first suffix and subsequent cached events.

These are complete **selected directional/multi-bit/event substages**, not
full-block or F5H completion. Upstream segment partition/accounting, UVLC/
quad interpretation, cleanup/significance/refinement block denotations,
placeholder/replacement sequencing and mixed routing remain required.
The inventory uses nineteen additional exact constructor/mutating-view
recipes, with fail-closed tests for each return binding, complete view,
old/final snapshot and function/model pairing. Scope lookup, mutable-parameter
completeness and expression matching are unchanged. Sixteen contracts have
actual internal production callers and are indexed. Three standalone public
APIs (`HtForwardMagSgnReader::read_bits` and both public refinement `read_bit`
adapters) are proved and their recipes tested against real API tests, but have
no internal decoder callers. They are not disguised as internal helper calls
or indexed through a wrong same-named method. The exact-root verifier checks
all these actual contracts independently of the non-exhaustive source index.
The next complete interpretation stage connects the actual UVLC prefix,
suffix, combined value and both U-mode decoders to the complete cleanup
reader state. Every native mode/length is covered, not just successful
prefixes: a true suffix bit above bit seven is rejected after consumption,
whereas zero bits above the result width may continue. Read failures precede
that width check. Initial mode three retains its special long-prefix route,
and both modes retain their exact prefix/suffix read order and checked
arithmetic failure points.

The actual quad-word caller refines lookup into closed views of the unchanged
production tables, then context-zero MEL suppression, codeword validation,
advance and final tick. No table words/notices are copied or modified.
Equivalent explicit boolean/checked-add conversions and one shared checked
byte-conversion helper replace opaque standard-library callback composition;
they do not introduce a second executable interpretation algorithm.
U-pair results retain their native two-element arrays. Extensional content
and exact array equality use the existing pinned `vstd::array` equality fact,
not a new codec axiom or trusted escape. Prefix opacity only keeps caller
composition modular; actual producer bodies explicitly unfold their models.

The authorized nineteen directional and six interpretation registry recipes
are complete. The six interpretation contracts use the same exact whole-state
shape, preserving actual extra arguments and native tuple/array/word results;
their models, true production callers, proofs and fixtures are indexed.
Neither this source index nor successful local gates close full-block or
mixed sequencing. The models and a green solver run are not human endorsement
of T.814.

`HtPassGroup::from_packet_passes` now shares one verified free implementation
that returns the complete actual four-field group, retaining the static
public wrapper and all original native bounds/error behavior. This is an
input-relative grouping theorem, not placeholder/replacement execution.

The complete actual public segment parser now refines `ht_parse_block_segments`
through a public closed outcome projection of every result field. The sole
authorized foreign edit supplies the owner-local `resource_code_block_byte_limit`
view and exact getter postcondition. The parser model therefore uses the actual
selected `ResourceLimits` value, not a chosen or existential budget. Size
rejection precedes the exact CodeBlockBytes failure, which precedes Scup
interpretation and partitioning. All encoded/substream bytes, offsets,
directions, Scup and total bytes are included, retaining the observable
distinction between absent and present empty refinement. No public-parser
wrapper or successful-input assumption is introduced. Its complete outcome
shape is proved by the root. The non-exhaustive source index binds this
function to its exact outcome/model recipe and actual caller; negative tests
reject unbound, partial, swapped or unknown outcomes/models without any
matcher widening.

Existing public F6 limb/value, constructor, zero-test, right-shift, exact
checked-add, full-domain checked-left-shift and low-word contracts are now
available in this combined branch. The actual HT numerical reconstruction
consumers still need their complete result/reader-state relations connected
through these interfaces. No Tier-1-local magnitude implementation or trusted
shim is introduced.

### Complete cleanup metadata boundary

`decode_ht_cleanup_segment_metadata` now refines
`ht_cleanup_segment_metadata` on **every return**. The public
`decode_ht_cleanup_metadata` additionally composes the actual segment parser
with its real code-block byte limit before the metadata header/work stage.
There are no stream-validity, decode-success, sufficient-budget or selected
trace preconditions on either entry point.

The internal producer is indexed through its exact complete outcome/model,
actual segment view, width/height/maximum-U arguments, actual work-limit
snapshot and scoped coefficient-symbol caller. Fail-closed mutations reject
swapped inputs/limits, unbound/partial outcomes, wrong models and wrong
callers. The separately verified public facade currently has only API-test
callers and is not falsely attributed to the internal block path.

The semantic reading path includes complete deterministic word/member,
sample/quad, pair and row folds in `specs/mod.rs`, with full typed first-error
propagation. Checked step/absorption lemmas justify the actual loops. The
source is still one executable traversal: the existing bodies are moved to
word, append, pair and row helpers, not copied into a proof-only decoder.
Their internal geometry and allocated-length facts are established from
the actual header and loop bounds; reader/event/work and significant-count
domains are not restricted to successful states.

The helpers expose complete disjoint mutable frames. A failed word read
retains prior current-pattern/left-context updates and all actual reader
effects. An invalid significant edge sample retains earlier sample counts
but does not store a quad or tick. A counter error precedes the store; a
work error from the final tick retains the stored quad and updated count.
The row's previous-pattern vector is replaced only after the entire row
succeeds. Opaque prefix folds retain their exact first error and state.
Canonical unit-result postconditions are proved from the actual bodies to
compose these folds, not assumed from success.

All returned fields are covered: dimensions, every ordered quad field,
significant-sample count, MEL/VLC bit counts and MEL events, including final
collision and checked 32-bit counter conversion. Allocation requests and
tick/read order are preserved. The unused **private** cleanup constructor
adapter is removed; metadata and its two existing tests use the same proved
free implementation. Public reader constructors are unchanged. Three local
`too_many_arguments` style allowances keep immutable codec inputs and
disjoint mutable frames explicit; no verifier/trust/termination limit is
relaxed.

The four new HT-only state properties use fresh solver contexts
(`spinoff_prover`) so their finite mask/geometry queries do not perturb
unrelated existing incremental solver queries. Their bodies and all limits
remain checked unchanged; no F6/color proof is edited for solver sensitivity.

Independent literal regressions include nine suppressed quads across odd
rows/columns/pairs, exact 24-unit success versus 23-unit last-store failure,
each actual northern/western context input, invalid edge-sample partial
counts, native counter overflow before/after stores, and public
parser/header error priority. Existing nonzero, fused-byte, UVLC and
collision fixtures remain in place.

This complete metadata boundary is independent of numerical magnitude
reconstruction. The F6 owner has now supplied the requested full-domain
interfaces separately in `f7807fe3bc6b2d3ccc622e2d3998eb3a39927535`;
they are not merged or duplicated in this metadata head. A clean joined
baseline is required before consuming them for the next magnitude/plane
stage. Neither metadata nor its positive tests complete coefficient blocks
or mixed sequencing.

### Complete numeric MagSgn boundary

`reconstruct_ht_magnitude` now refines the deterministic
`ht_reconstruct_numeric_magnitude` result/state model on every return. Invalid
completed-U/bitplane parameters precede all reader operations. The actual
payload loop consumes LSB-first physical/stuffed/fill bits with the already
proved complete reader transition; every first read/counter/budget error
retains its actual final reader state. Sign and exponent are accumulated
alongside the full numeric value, not a low-word proxy.

Embedding, odd-center correction, centering, checked left scaling, right
division and zero rejection are one moved executable completion body using
the real F6 factories and full-domain arithmetic contracts. Its private
geometry facts are derived from the original public-entry checks; the
completion body itself admits every native 384-bit magnitude and exponent,
including capacity rejection. A checked modular-arithmetic lemma connects
the real low-word parity test to full-value parity. No arithmetic algorithm,
foreign source shim, assumed success or new limit is introduced.

The source index has a narrowly typed recipe for this one actual producer:
the complete numeric outcome and complete final MagSgn reader must equal the
listed model on the actual old reader and native arguments. The existing
every-mutable-parameter check remains active. Tests reject missing/old/wrong
final states, unbound/partial outcomes, swapped inputs and wrong models; this
does not introduce general expression matching or an API-root exception.

Independent fixtures cover sign/exponent/scaling and inconsistent native
embedded flags, zero-bit reconstruction without touching even over-budget
reader state, all six limbs at bit 365, stuffing and physical/fill budget
errors with complete literal cursor/counter states, native counter overflow
and centering/shift overflow.

The next actual cleanup-plane boundary reaches `CoefficientState::set_magnitude`,
which uses the foreign `Magnitude::limb(index + 1)` to store all five high
words. The owner now supplies its exact full-index
`Some(magnitude_limbs(self)[index])`/`None` result and a public pure six-limb
shape fact while keeping the representation closed. The actual stores and
signed-result/plane consumers still need their complete relations through
those interfaces; no shifted low-word replacement, assumption or duplicate
limb algorithm is used. Plane reconstruction, placement,
stencils and final padding/termination are not claimed by the numeric
producer theorem.

### Complete cleanup plane and raw producer interfaces

`reconstruct_ht_cleanup_plane` now has a complete typed-result relation over
the actual supplied plane dimensions, raw cleanup descriptor, arbitrary
metadata, native maximum-U/bitplane values and actual work cap. Its blank
allocation does not assume or reuse old coefficients. The ordered quad/sample
fold includes checked coordinates before clipping, scan/read/placement/count
ordering, every raw six-word coefficient and flag, both complete exponent
vectors with reset/max/overwrite/swap behavior, and the final real reader
padding/stuffing/work check. Failed private transitions retain their exact
partial plane, reader, statistics and stencil state. This is not refinement,
replacement/placeholder/mixed execution or a metadata-to-plane caller theorem.

The raw coefficient/plane interfaces retain malformed shapes and full native
legacy midpoint tags, including insignificant stale words and significant
negative zero. Six thin ghost denotations express existing field/record
projections in the already supported complete-model contract form; original
numeric, shape and field facts remain available. The source index reuses its
exact known projection/reader recipes and every-mutable-parameter checks,
rather than adding a generic expression fallback.

The old two-field `SignedMagnitude::new` was crate-private and, after the real
signed producer's equivalent literal construction, used only in two tests.
That now-unused constructor is removed and those tests use the same literal
fields. No public API, decoder result, sign policy, arithmetic behavior,
dummy runtime call or lint suppression is introduced.

For raw bypass, error states are not transactional: work-limit failure preserves
the consumed bit and incremented work counter; work overflow preserves the consumed bit
and old counter. Marker-padding overflow preserves the already installed
synthetic byte/eight-bit count, without consuming the bit or charging work.
The constructor's private free helper is shared by the unchanged public
`RawBitReader::new` wrapper and actual legacy decode path; there is no second
executable reader. Its contract proves the initial state and exact input-byte
claim. These stage contracts do not complete the F5L packet/MQ/pass epic.

A separately reference-qualified layered/tiled RGB16 all-style regression
identified three termination corrections. Later completed coding segments
may have zero payload bytes; initial empty blocks, unfinished empty segments
and empty HT inputs remain rejected. Empty raw predictable termination is
valid only before any coded bit is consumed. A complete final raw `0xff`
may retain its exact seven-bit `0x2a` termination byte without that byte being
an entropy decision. The model and exhaustive terminal-pair regressions cover
these corrected outcomes; no oracle expectation, budget or cap was relaxed.

The production placed-layer compositor uses the complete `source_over_pixel`
evaluator. Its executable contract equates the entire optional color/alpha
result with one model: invalid channel counts or active premultiplied samples
above alpha return no pixel; valid inputs produce all specified rounded
channels and alpha, preserving unused array slots. The loop invariant connects
all processed channels and untouched slots, not just one arbitrary scalar.
Checked conversions remain in the evaluator, and its contract rules out a
spurious conversion failure on valid inputs.

Fixed-size stack buffers gather the supported grayscale/RGB pixel before
evaluation and scattering; no per-pixel heap allocation is introduced.
The production `gather_composition_pixel` contract covers the entire optional
input tuple, not just individual successful reads. Its model uses the actual
planar sequence views and indices: grayscale-to-RGB expansion reads source
plane zero for every active destination color, other cases select the matching
plane, absent source alpha supplies opaque straight samples, and inactive
stack slots are zero. Missing active planes, color/alpha samples or excessive
destination channel counts return no tuple; valid reads cannot spuriously fail.
The finite-channel loop preserves each processed read pair and every untouched
slot. The gathered tuple is passed directly to the verified pixel evaluator;
missing reads still become the existing typed invalid-layer error before any
current-pixel store or work charge. This gather relation alone does not
establish earlier layer channel-map resolution or mutable canvas/layer semantics.

The production compositor calls `compose_planar_pixel`, whose contract equates
the status, all final color-plane sample sequences and the final alpha sequence
with `part2_composition_pixel_transition`. That model composes the actual
planar gathers, complete pixel evaluation and planar scatter. Both mutable
outputs participate in the same equality; it is not just a result flag or
one stored sample. The projection uses the real nested vector views.
Its contract also explicitly states that a rejected pixel leaves both entire
outputs unchanged. Destination prevalidation in the gather rules out a
late scatter failure in this complete transition.

The raw scatter helper separately models all outcomes: excess channel counts
write nothing, a missing destination sample leaves the already stored color
prefix intact, and a missing alpha slot leaves all successful color writes
intact. Its model identifies every changed sample and preserves all others.
Its loop relates the complete current nested-plane state to the initial
state plus the processed prefix. Ghost snapshots and pointwise frame
assertions connect nested mutable borrows to that relation; those snapshots
and assertions erase from Cargo builds. No new trusted codec body is added.
The complete transition validates before invoking this raw scatter and has
the stronger no-change rejection property described above.

The independent read/rational/store oracle checks 159,744 shape/representation
cases and the entire resulting buffers, including valid and invalid
premultiplied samples; 864 raw-scatter cases check successful and partial
failure states, unchanged-value stores, missing slots and extreme indices.
The existing placed-layer rational/geometry and work-order tests remain.
The pixel models use pure nested sample sequences. Their production contracts
project actual vector views at the boundary, so the modeled resulting state
can feed the next pixel without reconstructing executable vectors.

The actual `composite_placed_layer` return contract is explicitly guarded by
`result.is_ok()`. On that path it equates all final color/alpha samples and
the final work counter with one complete placed-layer success model. The
row/column loops retain the exact raster-prefix state and the affine charge
`initial_work + completed_pixels * (color_channels + 1)`. The prefix model
selects every source coordinate with the existing crop/scale equation and
every destination with the actual row-major canvas address. Its base and
successor lemmas are proved and invoked from the production loops; the
recursive definition is opaque by default to bound solver expansion, not
trusted or skipped. No verifier resource budget was increased.

The cached alpha-slice/representation pair and grayscale expansion flag are
explicitly connected to the supplied normalized layer. The alpha cache
retains explicit option cases for that proof relation, with
a statement-local `manual_map` style-lint allowance; verification is not
suppressed. Empty source and
zero-target error priority remain unchanged. Empty clipped rectangles now
return before row traversal: a regression with `u32::MAX` unvisited rows
must return within five seconds while preserving even unvisited malformed
planes and an already exhausted work counter. This removes work-free empty
row iteration without adding new accepted pixel data. Work overflow and
work-limit rejection still occur after pixel stores, with their existing
counter behavior; exact tests preserve that ordering. The success theorem alone
does not specify partial buffers on `Err`, prove valid inputs always succeed,
or establish normalization, layer/frame order or standard-edition conformance.
An additional, unconditional placed-layer postcondition now constrains every
return, including `Err`: the complete output buffers equal some valid prefix
of that same raster fold. The work counter is the initial count plus either
all stored pixels' charges or all but the last pixel's charge. The latter
case preserves the existing checked-work-overflow behavior after a store.
Empty source, invalid zero target and empty clipping preserve all initial
buffers and work. A constructive prefix witness and raster bound are proved
and used before rejection, after stores, and after charging, so no error exit
is justified only by the success guard.

This is a prefix-safety theorem, not an exact failure-position or error-cause
model. It does not assert whole-render rollback or sufficient-budget success.
Independent multirow RGB regressions check every work-limit cut in a six-pixel
rectangle, a missing sample on the second row, an uncharged pixel on overflow,
and the exact-budget success case, comparing all stored and untouched samples
and the exact counter/error. Runtime instructions and error ordering are
unchanged; the new witness assertions erase from Cargo builds.
The compositor additionally has an unconditional equality to a deterministic
budgeted transition model. Its state includes the actual typed result, every
color/alpha sample and the work counter. The model checks address fit before
reading pixels, validates the complete pixel before storing, then checks work
overflow and the configured work limit in the existing production order.
It retains the stored pixel with the old counter on overflow, and retains
both stores and the incremented counter on a work-limit error. The recursive
fold stops on the first error; a verified absorption lemma proves later
nominal raster positions leave that exact error/state unchanged.

The work-limit model is a closed projection of the real `ResourceLimits`
field, connected by the executable getter's proved return contract. Local
typed error helpers and the limit checker have exact result contracts; no
new error kind or offset is introduced. Explicit propagation branches keep
their frame proofs before returning, with statement-local `question_mark`
style allowances rather than suppressed verification. The previous complete
success and all-return prefix-safety contracts remain separate postconditions.
An independent 1,260-case replay grid checks color/alpha truncation positions,
work-limit cuts, initial counters near `u64::MAX`, exact typed error precedence,
all buffers and counters using widened arithmetic. This establishes selected
normalized placed-layer execution, not earlier normalization, layer/frame
order, parser-to-pixel semantics or standard-edition conformance.
Malformed premultiplied data is rejected before destination writes for that
pixel, including a malformed later channel. This intentionally strengthens
the previous private intermediate-buffer behavior; public render APIs still
return the same typed error and do not expose a partial image. Earlier pixels
may already be written, and work-limit checks retain their existing position
after successful pixel stores. No whole-render transaction is claimed.
The test-only unplaced compositor remains a separate scalar reference path.

The evaluator and scalar reference share the source-over helpers. Ghost-only proof calls in the executable helpers
instantiate multiplication bounds; ordinary Cargo builds erase those calls.
The paired models establish alpha numerator at most `65535^2` and color
numerator at most `65535 * alpha_numerator` for straight samples or valid
premultiplied samples (`color <= alpha`). The division model establishes the
nearest-integer interval, including upward ties, for every positive denominator.
The executable division widens to `u128`, including for full-width `u64` inputs.
The helper postconditions identify their actual return values as natural
numbers, without truncating the models to machine words. Numerator bounds and
the nearest-integer interval are exposed in these executable contracts; a
proved bounded numerator also yields a rounded result at most `65535`.

The pixel evaluator's loop retains the alpha numerator relation and complete
processed-channel prefix as invariants. Its proof assertions establish that
each computed color and alpha result equals its composed scalar model and fits
`u16`, immediately before the checked conversions. The complete transition
passes those exact color/alpha results to the proved scatter.
Both color and alpha stores use the same executable checked slice-store helper.
Its contract equates the returned flag and complete final slice with a model of
the initial slice and requested update. Successful writes preserve every other
sample, including when the requested value equals the existing value; rejected
indices preserve the entire slice. The composed transition contract connects
the complete stored planar state, through the checked conversions, to the
source-over models. Rejected transitions propagate the usual typed invalid-layer
error; resource/work accounting remains in its original order, after successful
pixel stores.

These relations connect the pixel models and successful placed-layer canvas
traversal to production mutations, not just standalone arithmetic lemmas.
They do not prove earlier channel normalization, all caller index/channel
selections or layer/frame ordering correct. The canvas theorem covers the
selected successful placed-layer transition, not every failing render path.
No-change rejection of one store does not
establish transactional failure semantics for an entire render. Caller
rejection and checked conversions remain in place.
Placement uses the selected edge-aligned nearest-neighbor equation
`floor(position * source_extent / target_extent)`, with the full target extent
retained when the canvas clips the copy. Its executable helper proves the
natural-valued result and source-offset bound; the actual row/column loops
establish crop, canvas and addressing relations before passing the resulting
indices to the complete planar pixel transition.
The row-major helper computes `y * width + x` with proved `u64` intermediates
and a checked conversion to the platform's `usize`. The existing fallible
wrapper preserves its arithmetic-error behavior.

A flattening helper is not itself a coordinate validator: the placement loops
separately establish geometric bounds. Other callers receive the exact address
contract without a new blanket claim about their coordinate selection.
Geometric index bounds also do not prove that every supplied sample plane has
the declared cardinality; checked buffer access remains active. Empty-source,
zero-target and off-canvas behavior, and resource accounting order, are retained.
Independent rational-oracle composition tests are separate numerical evidence,
not a formal theorem about the entire compositor.

The `decode_output_shape_valid` and `component_output_shape_valid` helpers are
structural checks, not a codestream-to-pixel denotation theorem. Neither the
inventory nor the exact-root verification result establishes a complete
standards-level parser-to-pixel theorem. Numerical and metamorphic tests
exercise relations beyond these contracts; their evidence must remain
separate from formal guarantees.

Numerical agreement of irreversible transforms, fixed-point color conversion,
and nonlinear transforms requires separate conformance metrics and reference
outputs. The Rust/Verus toolchains, solver, and reviewed standard-library
contracts remain part of the trusted computing base.

## Changes to proof code

- Do not introduce codec `external_body`, `assume`, or `admit` escapes.
- Use explicit loop progress measures; do not bypass termination obligations.
- Add concrete postconditions/refinement evidence rather than disconnected
  model-only lemmas.
- Run the exact-root verifier and ordinary Rust tests.
- Review [supported-profile limitations](SUPPORTED.md) before strengthening
  public claims.
## Complete native general-layer chroma-key state

The actual `apply_chroma_key` producer now has an unconditional Result and
whole `OwnedLayer` relation to `part2_apply_chroma_key`. Key-count rejection
precedes checked area and preserves every input field. Success preserves
geometry, color space and every raw color plane, replacing any prior alpha
with the exact key-match mask and a straight-alpha flag. Ragged or missing
samples are nonmatches, zero channels match vacuously and zero-area layers
retain their native behavior; no normalized-layer premise is introduced.

The real source lookup and value comparison use explicit matches so their
semantics are visible to the pinned verifier without a new trusted adapter.
They preserve the original optional-value comparison. Loop-prefix predicates
live in proof support, while the auditable model describes per-channel and
whole-pixel meaning. Both directions of the quantified prefix relation are
proved with shared explicit triggers.

Independent native tests cover 6,480 raw layer/key/old-alpha contexts,
131,072 all-u16 matching/nonmatching sample-key pairs, zero geometry and
key-count-before-large-allocation rejection. One finite exact inventory recipe
binds the complete final owner, original owner and actual keys; adversarial
mutations retain all existing rejection checks and require the real
`decode_general_compositing_layer` consumer.

This is one bounded F2 producer. The separate opacity chroma-key path rejects
missing samples rather than treating them as nonmatches; it is not silently
changed or included here. Raw-key normalization, registration/sampling,
opacity and complete F2/F4/F8 composition remain separate work. Whole-root
and hosted qualification must match the delivered source before acceptance.
## Complete native registration extent and geometry admission

The real `registered_extent` now refines its complete typed-result model over
all four native u32 inputs, including zero grid, checked arithmetic, rounding
headroom and u32 result conversion. Explicit checked stages and the real
conversion match preserve the original evaluation/error order without a
trusted closure adapter.

The real registration producer now shares one `registered_layer_geometry`
preparation body. It derives ratio/grid admission, horizontal then vertical
extent and native checked area from the original dimensions and full raw
registration descriptor. Codestream identity remains unobserved by this
geometry operation. No normalized shape, successful preparation or adequate
allocation premise is supplied; existing registration raster loops use the
actual result and preserve their behavior.

Independent u128 ceiling references cover 4,096 full native extent frontiers
and 16,384 registration combinations, including zero ratios, maximum offsets,
typed overflow and zero area. Two finite exact contract recipes and negative
mutations bind every actual input and result to genuine production consumers.

This closes geometry preparation only. Complete registered color/alpha raster
sampling, raw-key normalization and opacity remain open F2 work; F4/F8 and
independent conformance are not implied.
## Complete native registered pixel sampling and partial buffers

The actual registration raster now calls the sole `copy_registered_pixel`
producer, whose full Result/color-buffer/alpha-buffer relation holds for raw
source owners, coordinates and destination planes. Source index precedes
destination index; every color copy precedes alpha lookup/storage. Missing
source or destination words preserve all earlier color stores and leave alpha
unchanged; later alpha failure retains the complete copied color state.
Absent source alpha produces the native opaque value. No source/target shape,
normalized-coordinate, successful-read or admitted-budget premise is supplied.

The shared real color-store helper preserves the complete nested-vector
state and slice extent. Ordered prefix composition and error absorption are
proved in proof support. The loop retains real checked-address and original
alpha facts, and reuses the existing proved structural unit-Result lemma.
Explicit optional lookup replaces only the original opaque closure call,
without new allocations or changed native evaluation/error policy.

Independent wide-index replay covers 24,000 raw source/destination/alpha/
coordinate contexts, including empty/ragged planes, more than three channels,
partial prior-color stores, default and malformed alpha, zero width and maximum
coordinates. Two finite exact recipes bind every mutable buffer, complete
final state and actual input; fabricated consumers and partial/guarded/wrong
bindings remain rejected.

This closes the actual pixel producer, not all outer registration traversal,
opacity, raw-key normalization or F2/F4/F8. Frozen whole-root/local/hosted
qualification and owner-main acceptance remain explicit.
## Complete actual native registration raster

The original `register_layer` now refines one complete Result/output model
from the actual raw source owner, full registration descriptor and both grids.
It derives geometry, the real zero-initialized buffers, checked row/column
coordinates, all skipped/outside samples, ordered real color/alpha pixel
stores and the final source-alpha representation flag. No successful geometry,
normalized input, source/store outcome or adequate-budget premise is supplied.

One real row body composes the native checked-coordinate logic and existing
pixel producer. Its full mutable-buffer relation preserves prior stores on
every later coordinate/source/alpha failure. Row/column folds and error
absorption are proved separately. Naming the original zero-plane seed exposes
the pinned standard-library clone facts; allocation/clone operations are not
replaced or trusted anew.

Independent wide-integer raster references cover 209,952 raw geometry/
ratio/grid/offset/channel/alpha/representation cases. Direct row regressions
check prior alpha before late horizontal coordinate overflow and no mutation
before vertical overflow. Two finite exact contract recipes bind the whole
owner result, all row buffers and every original input to real production
consumers, including adversarial rejection cases.

This closes actual registration, not complete opacity/raw-key normalization,
F2/F4/F8 or independent conformance. Exact frozen whole-root/native/reference/
resource/hosted and owner-main acceptance remain required for delivery.
## Complete actual raw chroma-key normalization

The actual `normalized_chroma_keys` now refines a complete input-relative
Result/key-vector model over raw bytes, channel count and bit-depth metadata.
Variable metadata rejection precedes precision validation, which precedes
exact byte cardinality. Real big-endian reads, low-bit masking, signed bias,
rounding and complete ordered key output have no successful-read or
pre-normalized-key premise.

Native checked byte assembly is explicit. The redundant bounded mask loop
uses the equivalent checked shift, and normalization shares the existing
proved actual unsigned-color scalar instead of maintaining a second arithmetic
implementation. Admitted precisions and masked values prove all scalar failure
branches unreachable; original typed metadata/length errors remain. No solver
budget, trust, cap or numerical-tolerance change is introduced. Loop-only
byte bounds remain in proof support; raw-byte and signed scaling semantics
remain auditor-facing.

Independent u128 references use arithmetic signed rotation rather than the
native XOR. They cover 23,040 depth/channel/length/pattern frontiers, every
signed and unsigned u16 raw word, Variable metadata priority, and38-bit
padding/high-bit cases. One finite exact result/input recipe and adversarial
mutations require the two genuine production consumers.

This closes the uniform byte-input producer including Variable rejection,
not per-component descriptor preparation, opacity, complete F2/F4/F8 or
independent conformance. Frozen full-root/hosted/main acceptance remain explicit.
## Complete actual per-component chroma-key preparation

The actual `normalized_chroma_keys_for_components` now derives its complete
Result from original bytes and ordered native precision/sign descriptors.
Every descriptor is validated and its byte count charged to the checked sum
before payload-length admission. The second traversal executes actual slices,
the proved one-channel normalizer, first-key lookup, append and final offset
commit. No successful descriptor/normalization/read result is supplied.

Its genuine append body has a complete Result/key-vector/offset relation for
raw descriptors, keys and offsets, including usize overflow and all first
errors. Failures preserve both owners; success appends before offset commit.
Validation and assembly folds/error absorption live in the model and proof
support respectively. Consumer links follow the actual moved normalizer edge.

Independent integer references cover 6,084 descriptor/payload cases and1,470
raw append/prefix/offset cases, including invalid precision before malformed
payload and maximum-offset overflow. Two finite exact recipes reject partial
owners, wrong primary inputs, guarded results and invented consumers.

This completes the raw per-component input producer, not opacity, complete
F2/F4/F8 or independent conformance. Frozen full-root/MSRV/local/hosted and
owner-main acceptance remain explicit delivery gates.
## Complete actual local opacity state and strict chroma policy

General-layer and opacity chroma-key updates now share one real traversal
with an explicit native policy. General missing samples remain nonmatches;
strict opacity still rejects any visited missing sample, including after an
earlier color mismatch. Both complete Result/whole-owner relations preserve
all original values on error and update only final straight alpha on success.
Strict source coverage is derived from actual reads, not a caller premise.

The actual flag-only opacity update now has a complete raw-owner relation:
existing alpha samples and all geometry/color values are preserved, only the
representation flag changes, and missing alpha reports the actual supplied
box offset without mutation. The original file-level branch executes these
same sole producers and retains its metadata/channel/header/key ordering.

Independent matrices cover 12,960 policy/raw-owner contexts and1,296 flag/
offset cases, including malformed geometry/planes, empty channels, mismatches
before missing samples and maximum offsets. Two finite exact recipes require
complete owners, all original keys/policy/flag/offset bindings and real callers.

This closes local opacity mutations, not external decoded/registered-alpha
copy, complete file preparation or F2/F4/F8. Every frozen full-root/MSRV/
native/reference/resource/hosted/main delivery gate remains explicit.
## Complete actual external-alpha copy and scratch state

The real external-opacity path now executes one complete
`copy_registered_layer_opacity` producer. Its Result/whole-owner model derives
first-color admission before target area, zero initialization, minimum copy
rectangle, all actual pixel/row stores and final-only alpha/representation
commit from the raw target and registered source. Source alpha and later
color planes remain deliberately unobserved. No normalized source, prepared
mask, successful read/store or budget premise is supplied.

The sole pixel/row bodies preserve target-before-source checked-address
ordering and source-read-before-destination-store behavior. Their full scratch
relations retain prior stores on later failure, while the target owner remains
unchanged until the whole copy succeeds. Column/row error absorption is proved
separately and bound to real input/output state.

Independent wide-index references cover 31,104 raw target/source/rectangle/
representation cases and4,096 pixel/index/plane cases, plus a late-row partial
scratch regression and first-color-before-huge-area rejection. Three finite
exact recipes require all original owners/coordinates and complete final state.

This closes actual external-alpha copying, not the complete parsed-file
opacity preparation/dispatch or F2/F4/F8 joins. Full-root/MSRV/local/hosted
and actual owner-main acceptance remain separate delivery gates.
## Actual decoder Part2 style admission and raw depth observations

The actual `validate_part2_coding_style` now has a complete native Result model
over the original style and real DSC/ADS/ATK registries. Missing decomposition
is checked before arbitrary-kernel presence; unobserved raw style/descriptor
contents remain deliberately unvalidated. Native registry lookups preserve
original first-match behavior and prove precisely the presence observations
used here, not unobserved descriptor contents or successful execution.

Ordered component-depth comparison now refines equality of every raw precision/
sign pair, including zero/out-of-range precision, duplicates and length
mismatch. Its getter exposes those same values. `validate_executable` retains
its actual unconditional Ok behavior; no new policy rejection is invented.

Independent tests cover 262,144 style/registry/transform contexts, all native
lookup indices/duplicates/first-pointer identities and2,560 raw depth cases.
Two finite exact recipes and adversarial bindings require the genuine
`validate_part2_execution` consumer. Internal style visibility supports these
same-crate raw tests, not a new public API.

This is an F8 prerequisite for actual decoder results needed by remaining
F2/F4 file joins. Whole layout admission, planning, compressed/parsed decoder
and frame composition remain open. No normalized input, lookup/decoder outcome
bank, conformance or whole-F2/F4/F8 claim follows. Frozen full-root/MSRV/
local/hosted/main acceptance remain required for delivery.
## Complete actual parsed-layout execution admission

The original `validate_part2_execution` now refines a complete Result over raw
main/tile execution headers, original component styles and the native logical
component count. It executes the actual executable observation, style lookup,
style admission and ordered raw depth comparison. Main components precede all
tile headers; each tile's components precede its nonempty-CBD agreement check.
Empty CBD retains its native bypass, including contradictory raw metadata.

The real single/all-component and tile admission phases have complete input-
relative Results, with proved prefix/error absorption. No valid-layout, style,
successful validator/decoder result or sufficient-budget premise is supplied.
Full and selected actual decode-layout callers use the same sole bodies.

Independent literal registry/depth and native-qualified style-lookup references
cover 12,960 raw count/physical-owner/style/header/CBD combinations, including
zero/MAX counts, malformed unused metadata, main-before-tile and style-before-
CBD first errors. Four finite exact recipes and adversarial binding tests
require the genuine caller chain; moved style/depth edges are updated.

This closes parsed-layout admission, not actual packet planning, decoder
components, file normalization/opacity, frame output or complete F2/F4/F8.
Frozen full-root/MSRV/native/reference/resource/hosted/main acceptance remain
required, with no normative/conformance claim.
## Complete actual tile-component geometry

The original `ImageSize::tile_component_bounds` now has a complete raw-input
Result relation: actual tile clipping/checked geometry, ordered logical and
physical component admission, six registered ceilings, nonempty extents and
relative image coordinates. Raw descriptor precision/sign remain unused;
registration/subsampling and contradictory counts are not normalized away.

The existing registered-ceiling computation is shared with the native decoder
typed-layout output-region helper, retaining its distinct zero-divisor error kind.
An explicit zero/one rounding branch exposes the same boolean conversion to
the pinned verifier without a new trusted standard-library adapter. Three
finite exact-input/result recipes, all 65,536 registration words and 168,750
independent raw tile/descriptor contexts cover both native consumers. This
does not close packet planning, file decoder output, or whole F2/F4/F8.
## Complete actual resolution-style traversal

The original `CodingStyle::resolution_downsampling` now derives its complete
Result from the raw level/direction array, preserving resolution admission,
real stage lookup, ordered horizontal/vertical checked scaling and the first
overflow or physical-array error. Its sole actual stage helper has a complete
raw-scale Result; proved prefix steps/error absorption connect the loop.
`precinct_exponents` returns the original raw pair or exact range/array error,
without validating unused fields or imposing the caller's exponent limit.

Three exact input/result recipes and independent all-u8 level/resolution,
raw scale, overflow, physical-array and precinct-pair regressions bind the real
planner/subband consumers. No normalized style, lookup/arithmetic success,
trust adapter, termination opt-out or second executable codec is introduced.
Complete resolution geometry, packet planning and F2/F4/F8 remain separate.
## Complete actual resolution geometry

The original whole-image and optional-tile resolution geometry APIs now have
complete raw-input Result/all-field relations. Real component coordinates and
resolution-style traversal produce checked extents, code-block/precinct grids
and products in original error order. The whole-image branch intentionally
ignores registration while the tile branch uses registered clipping; the
legacy reported subbands value remains3 for every nonzero resolution.
No incidental policy was corrected or normalized during this composition.

Coordinate and floor helpers, real field-view equalities, three exact native
consumer contracts and the curated public boundary connect every result to
original metadata. Independent wide-arithmetic tests cover129,600 complete
geometry contexts plus27,000 raw admission/zero-sampling/error-priority cases.
The prior independent tile oracle is reused rather than duplicated. Complete
packet planning, decoded-component production and F2/F4/F8 remain separate.
## Complete actual component packet-grid producer

`derive_packet_grid_for_components` now derives its complete Result/full
PacketGrid from raw image/component-style/selection/limit metadata. The
actual shared first phase validates every component's resolution/selection
before geometry. Real geometry, subband deltas, selected-only code-block
accounting, zero padding and all-resolution precinct counts feed the sole
proved packet-grid constructor. Discarded finest geometry is still evaluated.
No admitted grid/counts/geometry or successful budget premise is supplied.

Mathematical suffix runs and a proved component-to-resolution transition
connect both original loops. The caller directly invokes the existing proved
free constructor, preserving its sole body and all runtime order; conditional
static-method attributes on the pinned macro could not be annotated safely,
so no internal marker, new trust, pin change or duplicated constructor is used.
The now-unused private forwarding method is removed; public constructors
remain unchanged.
Native equality observes every private grid field; independent geometry and
count-vector oracles compose with the previously independently tested factory.
2,744 raw admission contexts and230,400 full grid/selection/limit contexts
exercise complete states and first/late errors. Full packet-plan construction
and F2/F4/F8 remain separate.
## Complete actual subband admission and quantization

Raw quantization style/guard/step observations and logical/physical lookup now
feed the sole shared indexed/ScalarDerived step computation. The public
isotropic orientation-index API and actual subband-geometry helper retain
their different original admission policies; Derived observes step0 and
saturates its exponent while preserving raw mantissa and the supplied index.

`make_subband_geometry` has a complete Result/all-field relation, including
precision/gain overflow, zero range, quantization lookup, bitplane/ROI checks
and last-only checked extents. No raw step/depth/bounds normalization or
successful intermediate result is supplied. Both callers share the actual
computation; public boundary/native-consumer recipes bind four full contracts.
All-u16 lookup,147,456 raw public-index contexts and589,824 complete admission
contexts independently cover first/late errors and all returned fields.
Complete subband-vector/tile-plan construction and F2/F4/F8 remain separate.
## Complete actual component subband vectors

Public and optional-tile/ROI subband APIs now have complete raw-input
Result/ordered-vector relations. Actual component admission precedes real
coordinates and the original truncated 32-stage subband count/allocation.
The sole native per-resolution body derives scaling, phases, anisotropic
HL/LH/HH order and every geometry/quantization/bitplane field. Actual growing
length supplies checked indices; initial LL keeps its fixed index0.

Mathematical suffix runs retain last-byte advancement, first/late errors and
the original final count check. No normalized bands/bounds/counts, supplied
geometry/lookup result or successful allocation premise is assumed. Native
vector ownership moves across the shared resolution helper without replacing
its allocation/growth algorithm. Independent reused scalar/coordinate oracles
cover207,360 full-vector contexts,900 raw admission contexts,2,048 raw count
styles and32 prefix/index-boundary cases including65535/65536 entries.
Full tile-plan/packet/decoded-component/file/F2/F4/F8 joins remain separate.
## Complete actual Tier-1 decoder initialization

The sole actual decoder initializer has a complete Result/every-field relation
from raw dimensions, significant-bitplanes, orientation and style. Original
bitplane admission precedes pass metadata and the proved zero-plane producer;
all initial legacy/HT/counter/buffer fields derive from that real computation.
The public new facade and actual planner reuse the same body; no initialized
decoder/plane result, normalized style or allocation premise is supplied.

Route forcing, multiple-set policy and magnitude-bound setters have complete
state relations, retaining every unrelated raw field and the unchanged owner
on invalid-bound errors. Four exact native-consumer recipes,10,976 raw factory
contexts,the entire u16 significant-bitplane domain and dense raw/sentinel
setter snapshots cover defaults, lazy style policy, first failures and all
state. No new trust, pin/budget/termination change or duplicate decoder is used.
Implicit-unit setters use their literal unit result with exact signature
guards and negative return-shape tests, not an invented executable return.
Full tile-plan/packet/component/file/F2/F4/F8 composition remains separate.
## Complete actual code-block planning primitives

The actual tile loop now consumes the sole checked lattice/clipping producer
and the configured decoder initializer. Full raw arithmetic and u16 narrowing
are modeled without assumed valid dimensions; zero extents intentionally
remain the decoder initializer's admission policy. Real initialization still
precedes multiple-set and magnitude-bound configuration, including errors
and allocation order. All returned decoder fields derive from actual state.

No supplied geometry/placement/decoder bank, successful budget or normalized
lattice is a premise. Two exact native-consumer recipes,165,888 independent
wide geometry contexts,5,760 configured-constructor contexts and the complete
byte-bound sweep cover boundaries and first failures. The full tile-plan
vector/precinct/packet/component/file/F2/F4/F8 joins remain separate.
## Complete actual precinct initialization

The actual tile planner and public precinct facade now execute one proved
constructor from raw execution vectors/style/limits. It preserves the original
execution-count/shape, cumulative block/work limit, decoder-length, context,
decoder-move and ordered tag-tree policy, including empty-list success and raw
coordinate/style observations. No admitted execution, prepared precinct or
successful lookup/tag-tree/allocation/budget result is assumed.

Owned prefix/context preparation has a complete Result/state relation. A
proved row transition connects real mutable execution buffers to mathematical
suffix runs, retaining untouched future rows and moving decoder vectors
without replacing their allocation/append algorithm.810 raw prefix/context
cases and28,800 full constructor/facade contexts compare all owned state,
ordered tag trees, limits and first errors using previously verified primitives.
Full tile-plan vector/packet/decoder/file/F2/F4/F8 joins remain separate.
## Complete actual component-plan metadata

The actual tile component loop now consumes one complete raw metadata
producer. Real style/reduction/quantization admission precedes route policy,
tile bounds, full output geometry, scaling, original image-origin position,
ROI lookup and actual computed subbands. All returned style/geometry/position/
subband fields derive from real inputs; no prepared metadata, bounds/bands,
lookup result or successful budget/allocation premise is supplied.

Raw component quantization and ROI getters have exact logical/physical
relations without inventing descriptor/shift validation. Three exact
native-consumer recipes, entire-u16 owner/ROI lookup cases and 115,200 complete
metadata contexts retain all output fields and first/late error policy.
The original body is shared without duplicate executable computation or
allocation-order changes. Full tile-plan/decoder/file/F2/F4/F8 joins remain
separate.
## Complete actual code-block decoder and placement vectors

The actual tile planner shares one owned vector producer for its nested
code-block traversal. It derives every decoder from the real configured
initializer, appends all placement fields in row-major order, preserves
incoming placement prefixes and derives flattened indices and selected-only
global counts. CodeBlocks precedes WorkUnits admission; geometry, initialization,
relative-position and index errors retain their original order. Empty shapes
retain the original lazy style/geometry admission.

Two complete native contracts and exact consumer-binding mutation recipes
cover raw lattice/clipping/shape/subband/style/HT policy/location/owned prefix/
count/selection/limits, not supplied initialized decoders or successful plans.
The nested mathematical suffix folds retain all owned state and error results;
their raw-input frame is an invariant, not a new input premise. The equivalent
typed limit literals and explicit fallible capacity match expose existing
constructor/standard-library behavior to the pinned verifier without new trust.
Independent wide geometry and flat-order composition tests compare every
decoder field and placement across 103,680 vector and 768 cell contexts.
Full tile-plan, decoded-component and F2/F4/F8 joins remain separate.
## Complete actual subband execution production

The actual tile planner now consumes one raw subband execution producer.
It derives checked intersections, block lattice and shape, then composes the
real configured decoder/placement vector factory and packet-row metadata.
An empty intersection preserves the original lazy style/bitplane/policy/limit
admission, while subband-end overflow still precedes that bypass.

Two complete exact-binding contracts cover raw band/block/subband/style/
policy/location/owned prefix/count/selection/limits without supplied lattice,
initialized decoders, prepared executions or successful resource premises.
Actual native views and a proved packet-field observation bind all output
fields without opening private executable representation or adding trust.
Independent wide intersection/lattice tests cover 10,368 raw contexts;
57,600 full composition contexts compare packet presence/metadata, every
decoder field, placement prefixes, indices and selected-only count/errors.
Full resolution/precinct/component/tile and F2/F4/F8 joins remain separate.
## Complete actual precinct planning from raw subbands

The actual tile planner shares a complete per-precinct producer. Checked
indices and raw subband lookups feed actual intersection/lattice/execution
and configured decoder/placement production; the real packet factory then
derives every private context/state/decoder/subband/tag-tree field.
Its source prefix, row-major flattened indices, selected-only global charge
and later local factory/tag-tree budgets retain the original error and
allocation order, including empty/ragged/over-three-source laziness.

The exact native contract and consumer-binding mutations admit no prepared
execution/decoder bank, initialized precinct, normalized range or successful
budget/allocation premise. A proved owned-state suffix fold derives the
whole output from raw source subbands. In 92,160 independent composition
contexts, wide geometry/flat-order references and the previously independently
qualified packet constructor compare every private packet field through the
existing shared test-only snapshot, plus all placements and global count.
Complete resolution/component/tile plans and F2/F4/F8 joins remain separate.
## Complete actual resolution-plan metadata and precinct-band coordinates

The real tile loop shares complete producers for resolution geometry/ranges/
precinct counts/first grid/band and block dimensions, then checked band
coordinates. Actual image/style/component/tile/resolution and raw component
origins feed real geometry and ordered style/scaling/direction lookups;
no geometry/count result, normalized origin or successful resource premise
is supplied. The actual caller obtains origins from its real component
metadata producer.

Zero subband delta retains the original bypass of precinct-count narrowing,
but does not bypass later exponent, split or size validation. Raw first-grid/
across/precinct/band arithmetic retains zero-divisor and ordered overflow
errors. Exact contracts and consumer mutations bind all fields and inputs.
207,360 independent raw metadata contexts and 46,656 wide coordinate
frontiers include large real precinct counts above u32 with zero/nonzero
band deltas.
Full resolution/component/tile vectors and F2/F4/F8 joins remain separate.
## Complete actual raw-owner component and selected tile plans

Actual component planning now derives all resolutions, real ordered precinct
states and complete component/band/placement fields from raw image/style
owners/quantization owners/ROI/component/selection/policies/limits. Existing
precinct prefixes are retained transport, not a successful result bank.
The actual selected tile planner composes first tile admission, the real
selected packet-grid producer and those actual component producers into every
private tile/style/grid/precinct/component field. Its public component-owner
boundary shares the sole body and original defaults.

Three complete contracts and exact consumer-binding mutation recipes bind
all raw inputs and complete outputs without prepared metadata/geometry,
successful plans, decoder banks or resource/allocation premises. Non-mutual
precinct, resolution and component suffix folds prove every intermediate
index, raw input and append frame internally while retaining first errors,
unused-field laziness, allocation order and global selected/local budgets.

25,920 complete component/prefix/count and 1,440 complete selected-tile
composition contexts compare all private grid/packet/component/placement
fields. They reuse independently qualified raw metadata/grid primitives and
the independent wide/flat-order precinct reference; they are not official
conformance vectors. Packet-to-decoded-component/file/F2/F4/final F8 joins
and uniform-owner facade construction remain separate.
## Actual packet execution to complete prepared components

Both real full and selected layout decoders now execute one owned post-plan
packet/reconstruction body after their unchanged plan production, metadata
admission and global accounting. Actual F5 byte execution mutates the real
precinct decoders; proved full-state/plane projection lemmas connect exactly
those decoder coefficients to actual F6/F7 reconstruction. Every prepared
component coordinate, extent, fraction bit, sample and MCT-work output is
bound, with the existing owned prefix transported unchanged.

No supplied decoded-plane/reconstruction result or callback, normalized plan,
successful budget/allocation premise or new trust is introduced. Direct real
field borrowing binds the complete owned plan while retaining the existing
full/selected packet entry points. The exact native recipe and 14,400 full
composition contexts retain actual byte/selection/error behavior, nonzero
MCT samples, raw ragged prefixes and work frontiers.
Whole raw layout/selection/file/F2/F4/final F8 and uniform-facade joins remain
separate; this is not a supplied-plan shortcut for those whole producers.
## Exact actual full and selected global plan accounting

Both actual layout callers share complete packet/precinct/codeblock
accounting from raw plan state, optional resolution counts, prior counters
and limits. The original full path checks placement-length totals after each
component; the selected path performs every raw placement/subband lookup and
resolution test before its final-only codeblock limit check. Empty components,
zero or mismatched layer fields, unused work limits and invalid indices retain
the original lazy/first-error behavior, not a new normalized-plan policy.

Two complete exact-binding contracts and terminating mathematical folds
derive every counter and typed error without supplied counts/results or
successful resource premises. 11,520 independent raw selected-component
contexts and 7,560 full/selected plan/limit/prior-counter contexts include
empty/malformed plans, separate stored grid/plan layers and u64 frontiers.
Whole raw-layout metadata/selection/file/F2/F4/F8 joins remain separate.
## Complete actual raw tile metadata admission

Both real full and selected layout callers now share one actual raw metadata
producer: first payload, exact MCT consistency, actual standard/arbitrary
kernel choice and ordered full/selected component-style preparation.
Every MCT array/collection/stage/transform field participates in exact
identity. Optional absence is not an empty graph, and unused descriptors
are not numerically normalized.

The actual maximum isotropic prefix retains physical32 truncation and lazy
stops; decoder wavelet agreement intentionally remains builtin-only, even
for equal arbitrary indices. First/MCT/kernel/style/reduction error order,
kernel lookup despite a false standard-MCT flag, checked u8 advancement before
discard subtraction and base first-three versus selected all-component
admission remain. The base emits an unused empty Vec with no heap allocation.
The old private receiverless optional-MCT facade was replaced by its sole
proved free body, preserving the pinned macro/compiler rather than adding
trust or changing pins.

Nine complete contracts and exact consumer-binding mutations bind all raw
inputs/results. Independent derived native identity compares 576 graph pairs;
67,584 raw isotropic, 254,016 raw style/reduction and 48,384 complete metadata
contexts cover logical/physical owners, missing/duplicate/raw invalid kernels,
MCT mismatch priority and actual first-payload identity.
Whole tile collection/layout/selection/file/F2/F4/F8 joins remain separate.
## Complete actual raw CAP lookup and HT profile policy

The actual layout callers' HT multiple-set, magnitude-bound and force-route
getters now derive completely from real raw CAP bit/physical-word lookup.
All-u8 part admission, absent/ragged words, invalid-mode nonvalidation, raw
multiple-set and low-five-bit magnitude fields, default74 and ignored
r_siz/block-coding/profile metadata retain their original behavior.

Eight exact native-consumer recipes bind raw owned field observations rather
than normalized profiles or supplied successful policy results. A terminating
actual mask/index suffix and a local proved bit-width fact preserve the
existing implementation without new trust, pin, budget or cap changes.
Policy definitions stay opaque until explicitly unfolded at their consumers,
isolating the solver context rather than increasing unrelated proof budgets.
18,432 raw lookup contexts and 1,572,864 policy contexts include every u16
capability word, physical frontiers and contradictory unused profile fields.
Tile collection/clone and whole raw-layout/file/F2/F4/F8 joins remain separate.
## Complete actual per-tile decoding from raw parts

Both actual layout callers now invoke one complete raw per-tile decoder.
Real first/MCT/kernel/style metadata and raw profile policy feed actual
selected grid/component/precinct/decoder planning; exact global accounting
then precedes real packet byte execution and F6/F7 sample reconstruction.
Every prepared component/position/extent/fraction/sample, global counter and
MCT-work field is derived from actual raw tile parts/image/profile/mode/limits.
An existing owned prepared prefix is retained transport, not a result bank.

The exact native postcondition and consumer-binding mutations admit no
supplied successful plan, decoded plane/sample/reconstruction outcome,
normalized metadata or successful resource premise. 38,880 complete
composition contexts compare all output fields and first errors, including
empty/mismatched raw parts, full-versus-selected admission, nonzero MCT output,
u64 counter/work frontiers and ragged unused prefixes. References reuse
independently qualified metadata/profile primitives with independent wide/
flat-order plan/precinct/accounting composition.
Actual tile collection/clone, whole layout/selection/raw parser/file/F2/F4/
final F8 and publication remain separate, not assumed by this producer.
## Actual owned metadata copy and ordered tile collection

The actual collectors now share one source traversal that still clones every
source part before filtering, including nonmatching parts. Same-order actual
Clone bodies replace only unsupported non-Copy derives required by this path;
the same field order and Vec/Option clone calls preserve allocation behavior.
Their posts prove complete logical data copies, not equality of opaque heap
allocation identities or an assumed cloned payload.

Every quantization/progression/MCT/Part2/nonlinear/kernel/registration/length/
header/flag/data field is observed without normalizing unused invalid data.
Two exact native-consumer recipes bind actual full payload copy and collection;
the internal clone chain and ordered suffix establish all source/append frames.
Method links resolve actual Clone trait impls and reject other or ambiguous
impls, instead of accepting a neighboring short-name function.
24 rich malformed raw payloads compare every native field and deep independent
buffers; 1,040 source-length/tile-pattern/query contexts retain duplicate order
and shared immutable byte slices. Both actual layout paths use the sole body.
Whole layout/raw-parser/file/F2/F4/final F8 joins remain separate.
## Source-derived raw owned payload operands

The mathematical tile-codec operands now use the complete raw payload
observations already proved by actual cloning and collection. Native payload
entry models remain thin projection wrappers over the same one mathematical
algorithm, not a second decoder. Rust execution, public APIs, bytes, style/
selection admission, algorithms, errors and every limit remain unchanged.

Actual source projections feed metadata/kernel/quantization observation,
planning, packet execution and reconstruction. New property proofs show
complete metadata, F5 byte execution and raw-tile sample/counter/work results
are identical for payloads with equal complete observations. These are
copy-congruence lemmas whose premises are established by real clone/collector
bodies, not additional codec validity or successful-outcome requirements.
No opaque heap-allocation identity, copy witness bank or decoded results
are assumed.

All affected native producers and existing semantic field/frame properties
are reverified. 1,440 ordinary Rust source-versus-independent-copy contexts
compare all real samples/counters/work and first errors, including nonzero
MCT samples. Existing exact native contract bindings remain.
Whole outer layout/parser/file/F2/F4/final F8 and publication remain separate.
## Complete actual full and selected parsed-layout decoders

The actual full/selected layout bodies now derive every decoded image
dimension/origin/component/descriptor/fraction/sample field from the raw
layout/request/limits. Actual Part2 admission precedes tile-count/cap65536
or actual selection validation; genuine source-owned tile collection then
feeds actual metadata/policy/planning/accounting/byte/reconstruction from
empty accumulated state, followed by real full/selected image assembly.

No normalized layout, successful plan/decoded components, callback/result/
copy witness banks or resource premises are supplied. Every intermediate
counter, source/append/work/selection frame and loop bound is proved from the
actual producers. The selected region is an actual fixed array; the internal
logical sequence-to-array totalization is proved unreachable at other sizes,
not an added input premise. Equivalent typed initial error literals and
explicit checked cast match expose existing behavior to the pinned verifier.

Two exact native-consumer recipes bind the public codestream callers' actual
bodies. 180 complete full and 2,520 complete selected composition contexts
compare all native image fields and first errors across raw empty/reordered/
duplicate parts, zero/overflow/count-cap geometry, reductions/regions/sets
and unchanged limits. Raw parser/typed final/file/F2/F4/final F8 and hosted/
main/publication remain separate.
