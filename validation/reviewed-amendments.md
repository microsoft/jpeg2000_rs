# Trusted engineering amendment registry

## Historical status after the native-review migration

This registry and its controller/tests are retained as audit history, not the
active admission mechanism after the separately reviewed migration is safely
activated. No new file-combination profile or registry adoption is required for
ordinary development. Existing records below retain their exact past meanings;
they are neither new source permissions nor normative certificates.
See [the replacement policy](../PROOFS.md#independent-review-and-technical-ci).
The migration itself requires verified live native protections before the old
required check is retired; changing this document cannot activate that policy.

This is policy data, not a proof or conformance certificate. The controller reads
only the copy from its trusted default-branch checkout, never a proposed branch.
An empty registry authorizes no protected changes. New or changed records are
proposals while this file is on a feature branch; only owner adoption on trusted
`main` gives them authority. Unchanged adopted records retain their history.

## Engineering decisions and proposed addition

| Record | Status and exact scope | Original evidence |
|---|---|---|
| `proposal-160` | Adopted through #167; the private parser-test relocation is now owner-merged in #160 | CI40608106332 / Verus40608106341; refreshed source qualification is retained in #160 |
| `proposal-164` | Adopted through #167; the standalone package-only `image` consumer is now owner-merged in #164 | CI40665820297 / Verus40665820275; refreshed source qualification is retained in #164 |
| `proposal-163-b4c6d67` | Adopted through #168; the source-complete package is now owner-merged in #163 | CI40713472934 / Verus40713472868; refreshed source and actual-main qualification are retained in #163 |
| `proposal-171-ghost-support` | Adopted through #172; the mechanical proof/view relocation is now owner-merged in #171 | CI40730904780 / Verus40729319509; refreshed source and actual-main qualification are retained in #171 |
| `proposal-174-tier1-tests` | Adopted through #175; private Tier-1 tests are now merged in #174 under explicit owner delegation | CI40772805265 / Verus40772806908; refreshed source and actual-main qualification are retained in #174 |
| `proposal-177-crate-rename` | Proposed exact owner-requested Cargo package/import/tooling rename; no decoder/model/proof Rust change | #177; original CI40789824278 / Verus40789825409; fresh source checks required after adoption |
| `proposal-180-decode-domains` | Proposed exact JBIG2-style decoder responsibility layout; executing contracts/body tokens and public API paths preserved | #180; original CI40978411701 / Verus40978411630; fresh source checks required after adoption |
| `proposal-183-remaining-domains` | Proposed exact remaining responsibility modules; existing native contracts/bodies, shared types and original ghost semantics preserved | #183; original CI41024230240 / Verus41024233243; fresh source checks required after adoption |
| `proposal-193-packet-metadata` | Proposed exact source-derived raw packet sum and metadata finalizers, result models and regressions; no source-integration or normative approval | #193; original CI41084399839 / Verus41084400145; fresh source checks required after adoption |
| `proposal-195-component-style-cache` | Proposed exact three-path duplicate-cache correction and latest-owner proof; eligibility only, not source approval | #195; original CI41110257458 / Verus41110257409; fresh source checks and separate review required after adoption |
| `proposal-197-tile-packet-admission` | Proposed exact seven-path actual PLT/PPT producer contracts, models and regressions; eligibility only | #197; original CI41135383976 / Verus41135383979; final refresh, full checks and separate source review required |
| `proposal-198-component-depth-registration` | Proposed exact seven-path component-depth/registration application and physical uniformity; eligibility only | #198; original CI41144651127 / Verus41144651097; final refresh and separate source review required |
| `proposal-200-decomposition-resolution` | Proposed exact nine-path actual DFS/ADS lookup, setter and owner-resolution contracts; eligibility only | #200; original CI41153180810 / Verus41153180822; final refresh and separate source review required |
| `proposal-202-sot-reader-marker` | Proposed exact eight-path actual SOT reader and marker-admission Result/frame refinement; eligibility only | #202; original CI41252094188 / Verus41252094124; final refresh and separate source review required |
| `proposal-206-tile-data-window` | Proposed exact seven-path actual tile-data range Result/final-reader refinement; eligibility only | #206; original CI41261831548 / Verus41261831538; final refresh and separate source review required |

Record adoption is gate eligibility, not permission to merge a source PR.
For every future record, refresh the source branch from accepted main after
adoption and require fresh complete checks before requesting source review.
Exact bytes, not a feature name or author's assertion, control eligibility.
No record permits unlisted model/proof Rust or controller changes, combined
amendments, or changed verifier/dependency pins and resource caps. An explicitly
adopted source-derived proof profile can admit only its exact listed additions;
gate eligibility does not establish their correspondence with a standard.

### Actual tile-data window and cursor commits

The proposed #206 record covers exactly the seven protected paths of the
already adopted `tile-data-window` profile, relative to accepted SOT main
`614f3509aac0117a5c171813bfa0578775e6dc37`. All fourteen older registry objects,
seventeen profile meanings, earlier models, pins and resource caps remain
unchanged. This is no new controller operation or combined source allowance.

Held source `58d4c50c5c97f8002fc1e686694ffad9641b1403` passed original
[CI41261831548](https://github.com/microsoft/jpeg2000_rs/actions/runs/41261831548)
and [Verus41261831538](https://github.com/microsoft/jpeg2000_rs/actions/runs/41261831538):
350 Python tests without skips, MSRV 687 library plus six example tests and
three doctests, 3,536 verified/zero errors for both root and the byte-bound
actual 173-entry/157-Rust-file archive, and all normal numerical, HT, consumer
and resource gates. All 4,591 previous observed items plus exactly the actual
helper, its closed Result projection and its source-derived model were
retained. The one new helper job is measured, not inferred from three
definition names or claimed as a source-coverage percentage.

The sole helper and its two real `read_tile_part` calls preserve the old body
after inlining. The zero-length path commits the located EOC boundary before
data-range or packet-metadata failure; the fixed-length path validates its raw
length/end/range but commits the cursor only after both packet finalizers
succeed. Complete Result, borrowed data bytes, reader/input/limits/work/packet
frames and every original error/partial-commit boundary are bound. The model
uses `specs/packet_input.rs`, not a widened root/SOT model profile.

This documentation-only proposal requires its own full qualification, fresh
Ready policy and independent record review before normal adoption and fresh
actual-main acceptance. Then #206 still needs final source refresh,
source/archive qualification, Ready policy, separate actual-source review,
guarded merge and fresh actual-main source validation. Record eligibility is
not source integration, lifetime analysis, normative or publication approval.

### Actual SOT reader and marker admission

The proposed #202 record covers exactly the eight protected paths of
`sot-reader-marker`, relative to accepted main
`1d20c2425b61029755a78f65916f60dc26d93f7e`. All thirteen earlier registry
objects remain unchanged. The fixed profile is already adopted; this is only
its exact source record, not another controller operation or source approval.

Held source `30102aad867548e6f07907f2db099f1072583650` passed original
[CI41252094188](https://github.com/microsoft/jpeg2000_rs/actions/runs/41252094188)
and [Verus41252094124](https://github.com/microsoft/jpeg2000_rs/actions/runs/41252094124):
349 Python tests without skips, MSRV 685 library plus six example tests and
three doctests, 3,535 verified/zero errors separately for the root and actual
173-entry/157-Rust-file package archive, and all normal numerical, HT, consumer
and resource gates. All 4,585 prior observed items plus six exact additions
were retained. Existing jobs were strengthened without a net obligation-count
increase; observed items and timing rows are not exhaustive function coverage.

The sole executing SOT reader preserves segment-reader partial commits and
the original marker/payload/count/length error order. Its full raw relation
includes all returned tile-part fields and the final reader frame. Three
executing marker predicates and four source-derived model definitions retain
the exact old admission sets and reader behavior. No new format feature,
normalized input premise, toolchain pin, trust or resource-limit change is
authorized.

This documentation-only proposal needs its own complete qualification and
independent record review. Normal adoption and fresh actual-main acceptance
must precede final #202 source refresh, fresh full gates and Ready policy,
separate actual-source review, guarded merge and fresh actual-main source
acceptance. The source remains draft and policy-held until those steps are
satisfied. No whole public decoder, lifetime, official conformance or
publication completion follows from the record.

### Actual decomposition lookup and owner resolution

The proposed #200 record covers exactly the nine protected paths of
`decomposition-resolution`, relative to accepted main
`3d9832086f6bf7a62551908a66e3ae99e2686602`. All twelve earlier registry objects
remain unchanged. The actual first-match DFS/ADS lookups, complete style setter,
executing resolution helper and ordered owner traversal use eight additive
source-derived models and three closed projections. Preserve raw duplicate
precedence, invalid/empty payload handling, component counts and physical holes,
stage limits, partial owner commits, tails and immutable parser frames.

Held source `92d08756a49eddaca6a4e1d927e12374b53a0a31` passed original
[CI41153180810](https://github.com/microsoft/jpeg2000_rs/actions/runs/41153180810)
and [Verus41153180822](https://github.com/microsoft/jpeg2000_rs/actions/runs/41153180822):
343 Python tests without skips, 3,535 verified/zero errors separately for the
root and byte-bound actual package archive, MSRV 680 library plus six example
tests and three doctests, and all 4,573 prior observed items plus twelve exact
additions. Observed items are not a function-coverage measurement. The measured
net increase of seven verification jobs includes five recursive model jobs
and two net actual-module jobs; projections and nonrecursive definitions are
not counted as independent SMT jobs.

This documentation proposal needs its own complete qualification and separate
review. After normal adoption and actual-main acceptance, #200 still needs a
final source refresh, complete fresh gates, a fresh Ready policy check,
independent actual-source review, normal guarded merge and fresh actual-main
validation. No outer parser/public-image composition, selected-edition
correspondence, official conformance or publication is approved here.

The separate deferred operation in
[tile-layout-input-profiles-authorization.md](tile-layout-input-profiles-authorization.md)
adds no source record. It must wait until #200 itself is normally merged and
accepted by fresh actual-main validation. Earlier forwards, including #203,
are spent and cannot authorize that operation.

### Actual component-depth and registration application

The proposed #198 record covers exactly the seven protected paths of
`component-depth-registration`. The fixed profile was separately adopted
through #199 and accepted from actual main; its forward permission is spent.
Current accepted main `327e02acf96643ffa90fdf380817ec0823a65f7f`
includes the independently reviewed cache and packet-producer increments.
Fresh CI41143644722 and Verus41143644713 accepted that main with 336 Python
tests without skips, 3,521/0 per root/archive replay and all normal gates.

Exact source `40d2711c808632170de1ed00a498f7390bb9db2e` passed original
CI41144651127 and Verus41144651097: 337 Python tests without skips,
674 library plus six example tests and three doctests on the MSRV,
3,528/0 per root and byte-bound archive replay, 173 archive entries with
157 byte-bound Rust files, and all existing numerical, HT, consumer and
65-record resource gates. All 4,564 prior observed items remain identical;
three actual helpers and six new models give 4,573 observed definitions.
Source-function coverage is not measured.

The real main-header application sites call the actual component-depth and
registration helpers in their original order. Complete results bind arbitrary
raw logical counts, physical slots, first-depth precision/sign, partial updates,
flags, unused tails and reader frames without normalized-image premises.
Actual SIZ/CBD/CRG reader joins and native behavior mutations exercise these
boundaries. Eleven reachable helper mutants were rejected on the same core
helper/model bytes; baseline and equivalent checked-increment controls passed.

The original helper focus has six obligations across three executing functions.
Three recursive model jobs are added and the two extracted inline layout
traversals remove two old jobs: net seven, not nine new functions or proof jobs.
The three nonrecursive wrappers have no standalone termination jobs. Actual
whole-root/archive measurements above establish the final counts.

This proposal preserves all eleven prior record objects and adds only the
exact component record below. The shared inventory retains every accepted
packet requirement plus the component requirement; helper/model bytes remain
identical to the earlier qualified component implementation. Adoption establishes
eligibility, not source review or integration. Final refresh, full checks,
fresh ready policy check, separate source review, normal merge and actual-main
acceptance remain required. Outer parser/public composition and independent
normative qualification are not completed here.

### Actual PLT/PPT tile-packet admission

The proposed #197 record covers exactly the seven protected paths of the
already accepted `tile-packet-admission` profile. The profile was deployed
through #196, with fresh actual-main qualification, and remains unchanged by
the later header-profile deployment. Fresh actual-main
CI41135235716 and Verus41135235586 accepted current profile main
`c9aba95c681f304eaf5dba2ef7568a5c96b47e18`: 335 Python tests without skips,
3,519/0 per root/archive replay and all normal gates. The #196 and #199
single-use forward permissions are spent.

Exact source `dad4c56a09013e623fea1cbf95c4e6d0b675326e` passed original
CI41135383976 and Verus41135383979: 336 Python tests without skips,
670 library plus six example tests and three doctests on the MSRV,
3,521/0 per root and byte-bound archive replay, 173 archive entries with
157 byte-bound Rust files, and all numerical, HT, consumer and 65-record
resource gates. All 4,560 prior observed items remain identical; the two
actual producer methods and two nonrecursive models give 4,564 observed
definitions. The models have no separate termination SMT jobs.
Source-function coverage is not measured.

The actual executed PLT/PPT branches become parser methods with complete
source-derived results, reader frames and partial counter updates. Preserve
main-header ownership conflict precedence, every raw next-index value,
index advancement before packet-length validation, work charges, the successful
`seen` update and sequential overflow commits. PPT conflict still precedes the
actual packed-fragment reader. Real segment/PLM/PPT/finalizer joins remain
executed producers, not prepared results or normalized input assumptions.

The source includes the accepted cache correction and preserves its successful
payload identity and native regressions. Packet helper/model/binding blobs
remain identical to the earlier qualified packet experiment; only shared tile
and test surfaces incorporate the separately integrated cache changes.
The exact before/after identities below bind this current combined base, not
the obsolete pre-cache tile/test blobs.

This proposal adds only the exact packet record, preserving all ten previous
record objects. It adds no controller, pin, cap, fixture, tolerance or other
source permission. Normal adoption establishes eligibility only. Refresh #197
from accepted record main, then require fresh full qualification, a fresh ready
policy check, separate source review, normal guarded merge and actual-main
acceptance. This is not completion of #133, outer parser/public composition,
normative correspondence, official conformance or publication.

### Exact duplicate component-style cache correction

The proposed #195 record covers exactly the three protected paths of
`tile-component-style-cache`. Its literal profile was separately reviewed,
adopted and deployed through #196. Fresh actual-main
CI41119479082 and Verus41119479105 accepted exact deployment
`9e577f1ebd075a8d81e81dbdcc82ac131c504ba9`: 325 Python tests without skips,
3,519/0 per root and byte-bound archive replay, all 4,560 observed items
unchanged and all normal gates. The #196 forward permission is spent.

Exact source `e25716fce02bb0f50f56681a30a3621842cc4ef8` passed original
CI41110257458 and Verus41110257409: 316 Python tests without skips,
666 library plus six example tests and three doctests on the MSRV,
3,519/0 per root/archive replay, 173 archive entries with 157 byte-bound Rust
files and all existing numerical, HT, consumer and 65-record resource gates.
All 4,560 prior observed project items remain identical; source-function
coverage is not measured.

The source replaces duplicated dense component-style snapshots with indices
into retained payload owners. Its actual payload identity and inductive
latest-owner/absence relations preserve inheritance, errors and native
persistence. Models, decoder entry points, pins, resource thresholds, fixtures
and oracle tolerances are unchanged. The related resource documentation is not
a protected source amendment.

Allocation attribution measured the duplicate cache at 1,901,056 bytes versus
4,096 for the index cache. Three native same-input pairs moved selected/full
RSS from 0.734-0.747 to 0.546-0.554; all 14 output hashes matched their original
independent expectations. These are finite observations, not a universal bound.
Instrumented heap measurements are not native resource-cap qualification.
Original over-cap measurements remain retained; no infrastructure-flake cause
or altered full-decode baseline is inferred.

This proposal adds only the exact record below, preserving all nine prior
record objects. It does not merge or review #195, approve #197/#198 or
decomposition-resolution source, or establish normative correspondence.
After normal record adoption, refresh #195 from accepted main and require fresh
complete qualification, a ready policy check, separate source engineering
review, normal guarded merge and actual-main acceptance.

### Source-derived packet metadata finalization

The proposed #193 record covers exactly the eight protected paths of
`packet-metadata-finalization`. The owner authorized bounded model/proof
development, and #192 separately adopted the exact controller deployment.
Fresh actual-main CI41092926417 and Verus41092926296 accepted that deployment:
315 Python tests without skips, 3,518/0 per source/archive replay and all normal
gates. The #192 single-use forward permission is spent.

Source `3eb0b67849d3f36428179bc03841ea552d08333d` passed original full
CI41084399839 and repository/actual-archive Verus41084400145: 311 Python tests
without skips, 664 library plus six example tests and three doctests on the
MSRV, 3,519/0 per replay, 173 archive entries with 157 byte-bound Rust files,
and all existing numerical, HT, consumer and 65-record resource gates.
All 4,554 prior observed items remain identical and verified; six added pure
definitions are four result models and two outcome projections. Nonrecursive
definitions do not each have a standalone SMT job. Source-function coverage
remains not measured.

The actual raw sum and length/packed-header finalizers derive their complete
results, original errors, input borrows and reader frames without prepared
outcomes. Existing model meanings and executing bodies remain unchanged;
the exact existing malformed-error constructor gains a proved postcondition.
No internal macro allowance, trust, termination escape, second executable
decoder, pin, tolerance or resource-policy change is included.

This record does not complete PLT production, inherited configuration, outer
parser/layout/public composition, independent normative review or official
conformance. Require separate green record adoption, fresh source qualification,
ready/green engineering review, guarded source merge and actual-main acceptance.

### Remaining runtime responsibility layout

The proposed #183 record covers exactly the 124 fixed protected paths of
`remaining-runtime-domain-layout`, not decoder modules or arbitrary directories.
The profile was separately reviewed and adopted through #182, deployed only as
the exact two authorized blobs, and accepted from fresh actual-main
CI41032672050 and Verus41032671904 originals: 308 Python tests with zero skips,
3,518/0 per whole-root/archive replay and all normal native, MSRV, resource and
real-consumer gates. Its single-use forward permission is spent.

The original corrected source
`bebe34dc1b0eab628d8f7b56d087ef611c638884` was qualified from full
CI41024230240 and whole-root/actual-archive Verus41024233243 originals:
306 Python tests without skips, 3,518/0 each, an exact 173-file/157-Rust archive
with actual pinned formatting and source binding, and all existing platform,
MSRV, resource and real `image` consumer checks.

All 1,636 original declaration projections, contracts, complete native bodies,
impl headers/generics/attributes and shared type/field tokens remain identical.
This includes four cfg-test helpers not observed by Verus; it is not measured
exhaustive source proof coverage. All 4,554 observed project rows match with
only 850 source-derived free-function namespace moves and 27 same-token
constant IDs (26 associated and one local). Canonical root type methods and
same-parent ghost identities remain unchanged. Actual proof output is never
rewritten to fit those expectations.

The first source proof correctly rejected implicit private-trait visibility
after a child move. Both unchanged Tier-1 symbol-trait implementations now stay
beside their original private parent trait. No specification was opened, proof
body changed, assumption/trust added, contract weakened or pin/budget relaxed.
The initial strict identity audit also rejected omitted constant expectations;
all 27 were then bound to identical source AST owners/tokens. Failed originals
remain retained, not counted as qualification.

The coherent source has 122 ordinary runtime files with a maximum of 1,321
lines; private tests and ghost support are separate real modules/includes with
their original logical identities. Models and proof Rust under `specs/` and
`proofs/` are unchanged. Existing public paths, native test identities, error
ordering, partial updates, ownership and resource behavior remain intact.
This is one Cargo/Verus decoder, not included executing chunks or a proof fork.

Decoder #180 is separately integrated and actual-main accepted. After normal
refresh from accepted profile main, draft #183 retains every qualified source
blob and has exactly the proposed 124 protected changes; its registry initially
matches accepted main. It remains genuinely policy-held until separate record
adoption. Accept fresh actual-main evidence after adoption, then refresh #183
and require fresh complete gates, original-artifact audits, a fresh ready policy
gate, separate ready/green engineering review, normal exact-head guarded merge
and fresh actual-main acceptance. No source merge, publication, visibility/tag/
history operation or normative/conformance certification is authorized here.

### Package-distribution choice

The adopted #163 record chose a source-complete archive rather than its
lean predecessor. Include the existing verification Rust sources and
technical reference so the actual unpacked crate supports the project's
pinned formatter and same-source Verus replay. Do not use formatter skips,
dummy specifications or a second decoder.

The archive accepted for #163 had 51 files, including all 35 runtime/model/proof
Rust files byte-identical to its source. Its compressed size was about 901 KiB
instead of the predecessor's 659 KiB. Ordinary builds still have zero default runtime
dependencies and do not enable ghost modules. No PDF, validation tooling,
default feature, decoder API or Rust implementation changes are included;
`publish = false` remains in force.

The source candidate was refreshed after both #160 and #164 landed, including
the new private-test file in Cargo traversal order. The record below therefore
uses the current original/proposed inventory identities, not the stale
pre-relocation proposal. Original evidence includes actual archive formatting
with Rust 1.93.1, repository and archive Verus 3,518/0 each, unchanged input
bindings, MSRV 660+3 from the retained archive and the real consumer's 37 tests
plus doctest. These checks are engineering evidence, not normative certification.

### Adopted decode-support layout

The adopted #171 record covers only `src/decode.rs`,
`src/decode/proof_support.rs`, the package inventory and the technical reference
inventory. It moves the existing 132-line reconstruction proof/view block through
a cfg-guarded include into the same logical `decode` module. Body bytes,
visibility and open/closed declarations are unchanged; recombination reproduces
the original decoder file exactly. Five proof-reference paths follow the move.
Attached contracts, loop invariants and executable bodies remain in place.

The recorded original source `233574e0392a7b460c6732d597008eca039f3971`
passed complete CI and repository/archive Verus with 3,518/0 each and all 4,554
observed project function identities retained, including the original lemma
namespace. The bound archive has 52 files and 36 Rust files; pinned formatting,
compiled native test identities, MSRV, resource and actual consumer gates passed.
These are engineering observations, not exhaustive source proof coverage,
lifetime verification or independent normative correspondence.

Source #171 was refreshed from accepted recovery main
`0e1158a1dc563474081cf52487295e00a684a0eb`, retaining all four exact proposed
blobs. After owner adoption through #172, it was refreshed again to
`884e2063c8a5054a17040ce47a59910769481e1d`; every source check, including fresh
policy gates, passed before source review. The owner merged #171 at
`24dd11ed3f32ae899802ce019076cda5e61fbe48`. Fresh actual-main CI and both
repository/archive proofs were independently accepted: 288 Python tests without
skips, 3,518/0 per proof replay, unchanged observed function identities and a
52-file/36-Rust source-bound archive. The earlier failed policy hold was not
waived or overridden.
This record cannot authorize Tier-1 cleanup, another module, a controller
amendment or a combined change.

### Adopted private Tier-1 test layout

The adopted #174 record covers only `src/tier1.rs`, `src/tier1/tests.rs`, the
technical reference and package inventories, and the binding-regression test
file. It moves the existing private `cfg(test)` module body without changing
the production/contract/proof prefix or its `tier1::tests` identity and private
access. The runtime-facing file decreases from 15,501 to 8,250 lines; the
standalone test module has 7,167 lines after pinned formatting.

Exactly 119 test references follow the move. The accepted ghost-support sources
and five proof-reference moves remain unchanged. The actual archive has 53 files
and 37 Rust files; all 666 compiled native test identities match the accepted
baseline. All 147 actual Tier-1 tests, missing/stale binding regressions, actual
archive MSRV 660+3 and real image consumer 37+1 checks passed.

The recorded original source `79c6f9aecd316e70fbcf323eda7fdbfd58c8c036` passed
fresh full CI and repository/archive Verus with 289 Python tests without skips,
3,518/0 per proof replay and all 4,554 observed project function identities
retained. Actual pinned formatting, source binding and native/MSRV/resource/
consumer gates passed. These are engineering observations, not exhaustive
source proof coverage, lifetime verification or normative correspondence.

Source #174 was normally refreshed from accepted profile main
`452d07bbc3eb059324dc2e6583b5c0097b50c881`, preserving all five exact proposed
blobs. After owner adoption through #175, it was normally refreshed again to
`aaa067e463c0a1de2d3b38616b15dd84c5c34279`; all source checks and fresh policy
gates passed before review. The assistant reviewed and normally merged it under
the owner's explicit delegation, without an admin/status override. Actual main
`c25a5b5999e0cb7062faa6882078a9e1f1ee5b8a` was accepted from fresh full CI and
repository/archive proof originals: 293 Python tests without skips, 3,518/0 per
proof replay, unchanged observed function identities and a 53-file/37-Rust bound
archive. The original failed policy hold was not waived or overridden.
This record cannot authorize another module, a controller/model change or a
combined amendment.

### Delegated engineering merges

On 2026-10-28 at 22:57 UTC the owner explicitly delegated engineering PR review
and merge to the assistant while completing publication preparation. This does
not make a feature branch authoritative, waive a gate or provide independent
normative adjudication. Separate policy adoption on trusted main, exact source
scope, fresh complete checks and original-artifact review still apply.
Delegated merges are recorded as delegated, not as independent human approvals.
Registry publication, visibility/tag changes and history rewriting remain
separate decisions.

### Proposed publication name

The new #177 record binds exactly the 23 paths in the fixed
`crate-publication-rename` profile to their original/proposed regular-file blobs.
Cargo uses `jpeg2000-decoder`; Rust imports and fresh proof reports use
`jpeg2000_decoder`. Examples, fuzz targets, the actual packaged `image` consumer,
archive binding, proof collector/schema/tests and related docs follow that name.
The repository remains `microsoft/jpeg2000_rs`; historical evidence and stable
validation protocol IDs are not rewritten.

The original source `5d99c8bc42f3ab932c54213519ab49d54880e8ee` passed full CI
and repository/archive Verus with 294 Python tests without skips, 3,518/0 per
replay, all 4,554 observed identities retained modulo only the exact requested
crate prefix, and a 53-file/37-Rust bound archive. Every decoder/model/proof Rust
byte, dependency version/checksum/pin, default dependency, MSRV and cap is unchanged.
Old-name and dependency-only proof evidence remains rejected.

This is gate eligibility, not permission to merge a red source PR or publish.
After separate adoption on trusted main, accept fresh main, normally refresh #177
and require every fresh source gate and original-artifact audit to pass. The
owner's explicit engineering delegation permits reviewed normal merges, not
admin/status overrides or independent normative certification.

An exception must first be proposed in a separate documentation-only PR. All
required checks on that PR must pass before review is requested. Owner adoption
of an exact record on `main` authorizes only those original/proposed regular-file
Git blob identities and that entire protected path set. Refresh the source PR
from the accepted main, run every required check again, and request source review
only when all checks genuinely pass. Combining a proposed record with its source
change does not authorize either change.

Records have `id`, `profile`, `source_pr`, `source_head`, `ci_run`, `verus_run`,
`rationale`, and `paths`. Each path maps to `before` (a blob ID or `null` for an
absent original) and `after` (a different blob ID). Evidence identifiers provide
an audit path; their presence does not certify the evidence. Owner review must
check the original source-bound results and the mechanical/behavioral argument.

Only bounded engineering path sets declared by the trusted controller are
supported. The existing records cover parser-test extraction, the standalone
image consumer and source-inclusive packaging. The #169
[decode-support profile operation](decode-support-profile-authorization.md)
was rolled back after required actual-main validation failed; its forward
permission is spent. The owner-adopted #170
[recovery authorization](decode-support-profile-recovery-authorization.md)
was deployed at `0e1158a1dc563474081cf52487295e00a684a0eb` and accepted from
fresh actual-main CI and repository/archive proof artifacts. It installed only
the fixed decode-support profile and added no source record. This source
record did not activate itself by changing a feature branch.
Normative model/proof targets and controller amendments remain
outside the source-record profiles.
Unknown fields/profiles, missing history, malformed trusted data, extra protected
files and non-regular file modes fail closed.

The owner-adopted #173
[Tier-1 test-profile authorization](tier1-test-profile-authorization.md) was
deployed at `452d07bbc3eb059324dc2e6583b5c0097b50c881` and accepted from fresh
actual-main CI and repository/archive proof artifacts. It installed only the
fixed five-path Tier-1 profile and added no source record. This proposed record
does not activate itself by changing a feature branch; the existing
decode-support record cannot authorize Tier-1 cleanup.

The #176 [publication-name profile authorization](crate-rename-profile-authorization.md)
was deployed at `8055a5e9f766a02fb40fd2526dd3ffd96eb96c3d` and accepted from
fresh actual-main CI and both proof replays. It added only the fixed profile,
not a source record. This proposed record cannot activate itself on a feature branch.

### Proposed real decoder modules

The #180 record binds exactly the 16 paths in `decode-domain-layout`, not another
module, controller/model amendment or a combined change. The qualified original
source is `39431e36cb8723365e951a2db203c4e7256d2a50`: a 367-line shared-type/
public-re-export facade, nine real runtime modules of 98-1,248 lines, separate
private tests and root ghost-only support. It is not arbitrary executing includes
or a second proof-free implementation.

All 146 executing declaration contracts/signatures/body tokens and shared type/
field tokens are preserved, apart from optional formatted parameter trailing
commas and private helpers becoming parent-visible where required. All 666
native test identities remain. Exact source preflight originals passed 300 Python
tests without skips, repository and actual-archive Verus 3,518/0 each, actual
63-file/47-Rust archive formatting/binding and all native/MSRV/resource/consumer
gates. All 4,554 observed identities remain with only the exact 124 declared
free-function module moves; root ghost-helper namespaces stay unchanged.

The fixed profile was separately adopted through externally reviewed #179 and
deployed at `b89ec2db65556587a4a69764c34f3e239b600ab7`, then accepted from fresh
actual-main CI/proof originals. It added no source record. This proposal cannot
authorize itself. Source #180 remains a genuine held draft until this separate
record is adopted with every check green. Then accept fresh main, normally
refresh source, require fresh complete checks and a separate engineering review
before its normal merge, and accept fresh actual main again. Agent reviews are
not independent human/normative approval; no publication is authorized.

```json
{
  "schema_version": 1,
  "amendments": [
    {
      "id": "proposal-160",
      "profile": "parser-test-extraction",
      "source_pr": 160,
      "source_head": "e929d74ae77ec277e55748012a13cbb48ac80bdd",
      "ci_run": 40608106332,
      "verus_run": 40608106341,
      "rationale": "Mechanical private-test relocation with unchanged executable/contract/proof prefix, compiled test identities, models, pins and resource policies.",
      "paths": {
        "src/codestream.rs": {
          "before": "d8c8066b191da8382ce10c2ca3eb6587d07a9b44",
          "after": "09f0b4369eabb7c05098d2aaa22041bfeadbe698"
        },
        "src/codestream/tests.rs": {
          "before": null,
          "after": "9317d9d81f43fb8d8d382e2a5733d8583789afc2"
        },
        "validation/expected-package-files.txt": {
          "before": "ef00ad4587c92a7c52365e5d6a1a0dec18f12005",
          "after": "026b291e83d7b551c092b5919886bc19b8b7b90e"
        },
        "validation/normative-coverage.json": {
          "before": "8053dd2c9ce66efdb4f39f75aa0e45539ccc7e9c",
          "after": "05237df10a29fd9e430180a0f7250da810db567f"
        },
        "validation/tests/test_framework.py": {
          "before": "28edc2ee48064bbb2693c44656705ab8934086fb",
          "after": "43da2a6f2e292bef0b9d411f772b59993f39403d"
        }
      }
    },
    {
      "id": "proposal-164",
      "profile": "image-consumer-probe",
      "source_pr": 164,
      "source_head": "bb5e67286d5c969ef23acba14e0f810193d74c33",
      "ci_run": 40665820297,
      "verus_run": 40665820275,
      "rationale": "Bounded standalone consumer of the actual package through image traits/hooks; no production decoder/model/API/pin/cap change or normative approval.",
      "paths": {
        ".github/workflows/ci.yml": {
          "before": "c4c373dc1604314d7588de438c33ed7182de7052",
          "after": "eaad74889b89bab5ca025282d4c53f9503d9e18c"
        },
        "validation/image-consumer-probe/.gitignore": {
          "before": null,
          "after": "b83d22266ac8aa2f8df2edef68082c789727841d"
        },
        "validation/image-consumer-probe/Cargo.lock": {
          "before": null,
          "after": "491fa432326017b6eb284354ebc9fbf595c5f56f"
        },
        "validation/image-consumer-probe/Cargo.toml": {
          "before": null,
          "after": "1735ac1955818412f4b4f266d080f0c418d137aa"
        },
        "validation/image-consumer-probe/src/decoder.rs": {
          "before": null,
          "after": "e8c36bb5ac7b5b12612fbc85163f44768e6eaa7c"
        },
        "validation/image-consumer-probe/src/lib.rs": {
          "before": null,
          "after": "40c4eff6e40c9b647ac4ec1e12a295cb956d8060"
        },
        "validation/image-consumer-probe/tests/adapter.rs": {
          "before": null,
          "after": "1eeb94542c3e000b2bc6631198437389eb8c2cea"
        },
        "validation/image-consumer-probe/tests/fixtures/gray.jp2": {
          "before": null,
          "after": "efc957bcd86ffef8f416081a790b1f64d6408bfb"
        },
        "validation/image-consumer-probe/tests/fixtures/rgb.jp2": {
          "before": null,
          "after": "b36f70e6d01316b056e30aa72aa05344f1181b55"
        }
      }
    },
    {
      "id": "proposal-163-b4c6d67",
      "profile": "source-complete-package",
      "source_pr": 163,
      "source_head": "b4c6d67af550c1ad69274f5d0f3db57b9d4b4cdc",
      "ci_run": 40713472934,
      "verus_run": 40713472868,
      "rationale": "Source-inclusive package preserves every Rust body and default dependency while requiring actual unpacked formatting, input binding and whole-crate proof replay; not normative approval or publication.",
      "paths": {
        ".github/workflows/verus.yml": {
          "before": "5f9cf1c43fae6163438514052162a743169d1621",
          "after": "11772c4f5f30a1f39dec8214a5a04741cd14782c"
        },
        "Cargo.toml": {
          "before": "b23f0d048482d5c3ab6e2767e0ca45a971ee2d95",
          "after": "d03202f88351757c86268f1f24102e21d0c90410"
        },
        "validation/check-packaged-source.py": {
          "before": null,
          "after": "80ea00883050923503738b845087122c6f6b4822"
        },
        "validation/expected-package-files.txt": {
          "before": "026b291e83d7b551c092b5919886bc19b8b7b90e",
          "after": "208d745650df83c5531c01f5ec7632f065da72e2"
        },
        "validation/tests/test_packaged_source.py": {
          "before": null,
          "after": "e48ca2c8f14499be0c40c00c31b5aa189544053c"
        }
      }
    },
    {
      "id": "proposal-171-ghost-support",
      "profile": "decode-proof-support",
      "source_pr": 171,
      "source_head": "233574e0392a7b460c6732d597008eca039f3971",
      "ci_run": 40730904780,
      "verus_run": 40729319509,
      "rationale": "Exact ghost proof/view relocation preserves the executable/contract/proof bodies and original decode namespace; original-file recombination and every observed function identity match. Not normative approval or source-PR merge permission.",
      "paths": {
        "src/decode.rs": {
          "before": "d2f27aff98662153229e6bb85be644150937c92d",
          "after": "afd81f4a1d9d17a79f952248e602798e544db53e"
        },
        "src/decode/proof_support.rs": {
          "before": null,
          "after": "848e266a5715993d226b5905fe112f035b183c87"
        },
        "validation/normative-coverage.json": {
          "before": "05237df10a29fd9e430180a0f7250da810db567f",
          "after": "26369b786df8431b476a3a67f83a454e8968375c"
        },
        "validation/expected-package-files.txt": {
          "before": "208d745650df83c5531c01f5ec7632f065da72e2",
          "after": "1afd84378f402a66b4a59b83fb17cdd5cbdaa454"
        }
      }
    },
    {
      "id": "proposal-174-tier1-tests",
      "profile": "tier1-test-extraction",
      "source_pr": 174,
      "source_head": "79c6f9aecd316e70fbcf323eda7fdbfd58c8c036",
      "ci_run": 40772805265,
      "verus_run": 40772806908,
      "rationale": "Mechanical private-test relocation preserves the complete production/contract/proof prefix, test-module identity and accepted ghost support. Exact evidence/package bindings and current compiled native identities are retained; not normative approval or source-PR merge permission.",
      "paths": {
        "src/tier1.rs": {
          "before": "97eb35539d40f4059a8bf735e2b8ff82baf26b32",
          "after": "be2b059c31a5b0db4571d8fc61e506c01fa69a47"
        },
        "src/tier1/tests.rs": {
          "before": null,
          "after": "24b8b6ed98ffbe15af1af8dcc216f9edbcf82767"
        },
        "validation/normative-coverage.json": {
          "before": "26369b786df8431b476a3a67f83a454e8968375c",
          "after": "c7436555216afc20d9cd86dfa7d0291deb2fd179"
        },
        "validation/expected-package-files.txt": {
          "before": "1afd84378f402a66b4a59b83fb17cdd5cbdaa454",
          "after": "a2d0538bf1db8f48537bb303bd55666df142ff16"
        },
        "validation/tests/test_framework.py": {
          "before": "43da2a6f2e292bef0b9d411f772b59993f39403d",
          "after": "bc1541157dfcb818f70546589e524dfb52d2afff"
        }
      }
    },
    {
      "id": "proposal-177-crate-rename",
      "profile": "crate-publication-rename",
      "source_pr": 177,
      "source_head": "5d99c8bc42f3ab932c54213519ab49d54880e8ee",
      "ci_run": 40789824278,
      "verus_run": 40789825409,
      "rationale": "Exact owner-requested package/import/consumer/fuzz/archive/proof-namespace rename. Decoder/model/proof Rust, dependency pins/caps and stable historical evidence unchanged; not registry publication or normative certification.",
      "paths": {
        "Cargo.lock": {
          "before": "8bd2cfd4db859e52593ffef32a436e636f2def4c",
          "after": "e1529eaee7b468eaedc9b412855ba1c6b7a1943e"
        },
        "Cargo.toml": {
          "before": "d03202f88351757c86268f1f24102e21d0c90410",
          "after": "5a8932f3becc76671045d98698508fa2c034e7b3"
        },
        "examples/validation_decoder.rs": {
          "before": "95387fb840dbf6e45b915b5eebea7ad866cea11e",
          "after": "66aa6e451b2566f14627bd47914ca3a56f4eae8a"
        },
        "fuzz/Cargo.lock": {
          "before": "4f1972085a9ebcd9bbbc7c5b34bc54b9d07307c5",
          "after": "bc77584a72e0be083f5b433263c88b0f7fbfb7d6"
        },
        "fuzz/Cargo.toml": {
          "before": "9d87c468400fe39962a8dc5d6b114f6a6ecbdd84",
          "after": "eb4e40065b493ed85c831a449c09a62d84257457"
        },
        "fuzz/fuzz_targets/arbitrary_codestream.rs": {
          "before": "07cfc2c1288c6d0ff7ae34a4d71ab0fc90f75d49",
          "after": "b5c0ee1542c2b710d72bcfe3b09f8392e5de4ffb"
        },
        "fuzz/fuzz_targets/arbitrary_jp2.rs": {
          "before": "90bcf9f45ca56d2151554450339c771744a847e4",
          "after": "9759038e292013ae4ae09d9851deb9959e59eafb"
        },
        "fuzz/fuzz_targets/arbitrary_jpip.rs": {
          "before": "57bb923b9a6ad3733cee4ff4baf5f33911545c52",
          "after": "ce72d23c9df8279298a12b8019b0e2e88f706822"
        },
        "fuzz/fuzz_targets/arbitrary_mq.rs": {
          "before": "04513d63730f65aaab15bf7ac5969ec4ac33257b",
          "after": "cc5fc8190c23a706c43657c3d6ee022737484dab"
        },
        "fuzz/fuzz_targets/arbitrary_packet.rs": {
          "before": "6f2f77cc0e1912920c20aff87c4c5b672a9bffa9",
          "after": "c260f37812189c02913025548d2098057b995a28"
        },
        "fuzz/fuzz_targets/arbitrary_tier1.rs": {
          "before": "beca6c0bf85136917c9026d0ab37a0432ebae0d5",
          "after": "36f7676206937b860792f12f838b3bb69992a2ac"
        },
        "fuzz/fuzz_targets/structured_framing.rs": {
          "before": "1ea887095caff78ee553fd920b4e14b30063fd5a",
          "after": "db1888cc91cc087bc2ec676ffa2d9d23aa5fa9b0"
        },
        "fuzz/src/lib.rs": {
          "before": "7745e45a0c15666771fde85f091d76c4af9f7181",
          "after": "5c1e2a124a43ff224bd8f0543a4048ee9f2a4b3c"
        },
        "validation/check-packaged-source.py": {
          "before": "80ea00883050923503738b845087122c6f6b4822",
          "after": "a5bd6e56be8adddde34c4490e5b5e761aa1ee6f3"
        },
        "validation/generate-proof-coverage.py": {
          "before": "08177cbe25df3a089e234adfd1d2443da40f2b30",
          "after": "b40eb49890b344e6aac81fe6511ee9e5d73fd95d"
        },
        "validation/image-consumer-probe/Cargo.lock": {
          "before": "491fa432326017b6eb284354ebc9fbf595c5f56f",
          "after": "0b6972accafa836b8390e4130f194073998fde2b"
        },
        "validation/image-consumer-probe/Cargo.toml": {
          "before": "1735ac1955818412f4b4f266d080f0c418d137aa",
          "after": "78c53f83fbd2a5ad79c917f4427a249d235a9f49"
        },
        "validation/image-consumer-probe/src/decoder.rs": {
          "before": "e8c36bb5ac7b5b12612fbc85163f44768e6eaa7c",
          "after": "07980025e18ebb70c88bb58c98564cee14d5c8a4"
        },
        "validation/image-consumer-probe/src/lib.rs": {
          "before": "40c4eff6e40c9b647ac4ec1e12a295cb956d8060",
          "after": "a149c2e239f2ea62e175ddb249066c536533b8b6"
        },
        "validation/image-consumer-probe/tests/adapter.rs": {
          "before": "1eeb94542c3e000b2bc6631198437389eb8c2cea",
          "after": "7470c1831535c9f5afd1e96c1a31b004c542fc67"
        },
        "validation/proof-coverage.schema.json": {
          "before": "e806b5dcdc2afd5ab8f861a9561e1a4b6d87701b",
          "after": "f73baf7545c4ed6445a37e4d7eff6babeed8d11b"
        },
        "validation/tests/test_packaged_source.py": {
          "before": "e48ca2c8f14499be0c40c00c31b5aa189544053c",
          "after": "45fd740d605cebb4cd5044592668bfc48f4411b3"
        },
        "validation/tests/test_proof_coverage.py": {
          "before": "76026ec16c80b96f29971d4a859ee7aed0a4e609",
          "after": "b1132139e7adce6620fab222198ecc7ff5ba043c"
        }
      }
    },
    {
      "id": "proposal-180-decode-domains",
      "profile": "decode-domain-layout",
      "source_pr": 180,
      "source_head": "39431e36cb8723365e951a2db203c4e7256d2a50",
      "ci_run": 40978411701,
      "verus_run": 40978411630,
      "rationale": "Exact real Rust decoder responsibility layout:146executing declaration contracts/bodytokens and sharedtype/fieldtokens preserved;666nativeidentities retained,124declaredmodulemoves only. Not a generic/model/controller exception, normative certification or publication.",
      "paths": {
        "src/decode.rs": {
          "before": "afd81f4a1d9d17a79f952248e602798e544db53e",
          "after": "bf7bb48e3951e301a53841f4c90a939cdf6aa448"
        },
        "src/decode/api.rs": {
          "before": null,
          "after": "b7c8c46667fe4188238868ca4a3943c2e40209ba"
        },
        "src/decode/arithmetic.rs": {
          "before": null,
          "after": "d95ce7f845b3fe49328af032aebdab75fb6331cf"
        },
        "src/decode/code_blocks.rs": {
          "before": null,
          "after": "ee5d14d2b97f5a46971fc4608c619eaecab6dcd6"
        },
        "src/decode/execution.rs": {
          "before": null,
          "after": "1ec7c63155383a43596098df07eccba4a924c1e2"
        },
        "src/decode/geometry.rs": {
          "before": null,
          "after": "cc4e7cbb7c8259e57235157b2cb09b4b8915c7cd"
        },
        "src/decode/output.rs": {
          "before": null,
          "after": "e2bc114a10d1760dfe927a3c65dc2e5d0a2c1544"
        },
        "src/decode/planning.rs": {
          "before": null,
          "after": "5ad7d96ad6368ce1559ee80fab387a30257db45c"
        },
        "src/decode/proof_support.rs": {
          "before": "848e266a5715993d226b5905fe112f035b183c87",
          "after": "6226e5852d6948024a648433c28800cc8df127f3"
        },
        "src/decode/reconstruction.rs": {
          "before": null,
          "after": "418edef885a155f556282f6d921e16c92b60478d"
        },
        "src/decode/selection.rs": {
          "before": null,
          "after": "d60a564133e39e2c47427ea23f63a9620f5f0d72"
        },
        "src/decode/tests.rs": {
          "before": null,
          "after": "b503ea0e4c830462ad13e3241713c0f21f27e07e"
        },
        "validation/expected-package-files.txt": {
          "before": "a2d0538bf1db8f48537bb303bd55666df142ff16",
          "after": "dad10d65b8755dab328cd6e969ef022ece8b5328"
        },
        "validation/framework.py": {
          "before": "2aa2f94580c51120b19bf3d4182e53eed4fb777f",
          "after": "868da3d7b50f1a022de8306e822557d2eaaaeff8"
        },
        "validation/normative-coverage.json": {
          "before": "c7436555216afc20d9cd86dfa7d0291deb2fd179",
          "after": "53f1b409b3910b26147979bbbf142cbe256dd18c"
        },
        "validation/tests/test_framework.py": {
          "before": "bc1541157dfcb818f70546589e524dfb52d2afff",
          "after": "ac92b5cd896d92a9634b8def13d61b4cb47a0956"
        }
      }
    },
    {
      "id": "proposal-183-remaining-domains",
      "source_pr": 183,
      "profile": "remaining-runtime-domain-layout",
      "source_head": "bebe34dc1b0eab628d8f7b56d087ef611c638884",
      "ci_run": 41024230240,
      "verus_run": 41024233243,
      "rationale": "One exact responsibility-based remaining runtime layout. Original1636declaration projections/sharedfields/contracts/nativebodies preserved;implicit private Tier1trait implementation scope preserved without opening specs;native666testIDs;850source-backedfreefn+27same-tokenconstantobservedIDmoves/all4554actualIDs otherwiseexact;173file157Rustsourcecompletearchive. Not a generic/model/controller exception, normative certification or publication.",
      "paths": {
        "src/codestream.rs": {
          "after": "c0eca7d199751c717c6b92ab976420075f2499e0",
          "before": "09f0b4369eabb7c05098d2aaa22041bfeadbe698"
        },
        "src/codestream/coding_markers.rs": {
          "after": "6f241a1a2aab33384c1a23766d0790778d784022",
          "before": null
        },
        "src/codestream/coding_style.rs": {
          "after": "9b19da5edabff4faeff7475b9c88f18e1be2ad55",
          "before": null
        },
        "src/codestream/decomposition.rs": {
          "after": "c1ce6dc3d16d14d636719790e9b5e8bcbe1851c9",
          "before": null
        },
        "src/codestream/extensions.rs": {
          "after": "f016e820bab1d68e265da480e090f43f28ab5a51",
          "before": null
        },
        "src/codestream/geometry.rs": {
          "after": "ff74cf8d00ad75a55f7ad523d7ecb405f27ec772",
          "before": null
        },
        "src/codestream/image_header.rs": {
          "after": "8097986505cb3648d8f286e5503cf2392010d825",
          "before": null
        },
        "src/codestream/layout.rs": {
          "after": "c91fb9df1748eaf10ae768f3e8c14db7b5e4d6a9",
          "before": null
        },
        "src/codestream/mct.rs": {
          "after": "8d08482a0ed0ec0b7b0f9df8473b5a58a2f6d4c2",
          "before": null
        },
        "src/codestream/mct_markers.rs": {
          "after": "eadc4526c863a75ff5657b0f7179a69907d45e0a",
          "before": null
        },
        "src/codestream/mct_resolution.rs": {
          "after": "220ea5c11c25185099078423492fbaac26a76549",
          "before": null
        },
        "src/codestream/packet_headers.rs": {
          "after": "fb96f69f20bbe0e053c1b35860ec238f4c39816c",
          "before": null
        },
        "src/codestream/part2_transforms.rs": {
          "after": "bd43d23642ed0d0e77de873e1db2096dee1a1701",
          "before": null
        },
        "src/codestream/profile.rs": {
          "after": "9a2f7d53776473d1c58b7649217e91469b0f23f5",
          "before": null
        },
        "src/codestream/proof_support.rs": {
          "after": "4a67d35f42dead523b857799582cab86e9bbb8d3",
          "before": null
        },
        "src/codestream/quantization.rs": {
          "after": "b2ed1bd063706a17623b64a5352cc7362423cbf5",
          "before": null
        },
        "src/codestream/reader.rs": {
          "after": "ebad4a7821322e99dfeeabed632b213ca8f2b4c2",
          "before": null
        },
        "src/codestream/tiles.rs": {
          "after": "567f93406ade6a5c50af705d54b8cba899318c88",
          "before": null
        },
        "src/color.rs": {
          "after": "ea37e29e63c8dae5c1da0fd5a387fa54053f0c3f",
          "before": "7fea42827f4d4733a5ef36db9d326b48ad412012"
        },
        "src/color/admission.rs": {
          "after": "86e5c3608ab2b4eb3f2e930bdc475e42677b2828",
          "before": null
        },
        "src/color/conversion.rs": {
          "after": "a731baf6d7ffeb9b35f9d38827d05780661012f1",
          "before": null
        },
        "src/color/crop.rs": {
          "after": "9728f7d0ea11627e2944ac9e6dac1ebd5c919997",
          "before": null
        },
        "src/color/geometry.rs": {
          "after": "10c9214fc5efe9b3ffb80b3bd7268f1adab1a6fc",
          "before": null
        },
        "src/color/normalization.rs": {
          "after": "0460b96a27fd33d9bf6d3c49730b5882c8286689",
          "before": null
        },
        "src/color/output.rs": {
          "after": "6e5182368ee76560f4b8accb81fa01711aab70b9",
          "before": null
        },
        "src/color/proof_support.rs": {
          "after": "9f31413fe87791a7864b3530b6aafabaface85ee",
          "before": null
        },
        "src/color/tests.rs": {
          "after": "60ba01df2ec1377226b9472871304d834ef635f8",
          "before": null
        },
        "src/image.rs": {
          "after": "b5bb3560414b82da031358c025c52ea62c6ec86b",
          "before": "58ef33c19287c5e002d7b1289e12fed1198ebfc8"
        },
        "src/image/arithmetic.rs": {
          "after": "e14eb646b8f31b1c3df97a1c41ff3a85f1e6deb9",
          "before": null
        },
        "src/image/assembly.rs": {
          "after": "fbcc7efe5a764f8c77b2824a7b903c4098ddfdfe",
          "before": null
        },
        "src/image/component_transform.rs": {
          "after": "d6c55777ddeec4d5a07ece9ce32a6091b8d8ffc0",
          "before": null
        },
        "src/image/layout.rs": {
          "after": "7899d572c0ff201a806eb225fae553241373afbd",
          "before": null
        },
        "src/image/mct.rs": {
          "after": "734f9f0c12bd6b64f872dd0ce1103dbb7b407750",
          "before": null
        },
        "src/image/mct_decorrelation.rs": {
          "after": "a82a0d22a8d3c8474c00ca496399f86b5ac7dbc1",
          "before": null
        },
        "src/image/mct_dependency.rs": {
          "after": "8f560d059a6ff066b9cc203e203d9e50f5cb06ce",
          "before": null
        },
        "src/image/mct_wavelet.rs": {
          "after": "9959e454cfab0736e17a2ca135828e237ab75b5f",
          "before": null
        },
        "src/image/nonlinear.rs": {
          "after": "32e7984b716a8fa7d9f614535e88a9d9a67a24dd",
          "before": null
        },
        "src/image/nonlinear_math.rs": {
          "after": "e471959d4b398ef27a9d247bc18862cbd2b0a2b3",
          "before": null
        },
        "src/image/proof_support.rs": {
          "after": "e15ba1dffbf600b335a6ac93b43748d5e3744b1d",
          "before": null
        },
        "src/image/samples.rs": {
          "after": "52710319562ec6cd8dabd94a9824ed3e0ad09bc7",
          "before": null
        },
        "src/image/tests.rs": {
          "after": "22e3fc198b5218ed4b013547e8efcb47a04e8a17",
          "before": null
        },
        "src/jp2.rs": {
          "after": "a8a76c7961cea12438623598dbca52129dd08e0f",
          "before": "44fb9ae346497ee138f177802bca53ece4ffd9cb"
        },
        "src/jp2/box_reader.rs": {
          "after": "c386bfee4ec32a2efd931c55f7de060ff89d18f5",
          "before": null
        },
        "src/jp2/color.rs": {
          "after": "2111009d1de851528f4614045945b7651bb376e3",
          "before": null
        },
        "src/jp2/composition.rs": {
          "after": "929cbab7d5f8e346e9b8a0ddfe02faf96f217888",
          "before": null
        },
        "src/jp2/container.rs": {
          "after": "81fe61ea4f03b1eb169a47d7612e550dac0aee7f",
          "before": null
        },
        "src/jp2/headers.rs": {
          "after": "79b351428ecaa93786e8cb5d28d02a7ce8da6fe9",
          "before": null
        },
        "src/jp2/metadata.rs": {
          "after": "a8eeb862809ddbabc57d0adf00667f1cab5f730c",
          "before": null
        },
        "src/jp2/proof_support.rs": {
          "after": "9bde6a18ed84695f119c486ea55344c8e1ab7ad8",
          "before": null
        },
        "src/jp2/tests.rs": {
          "after": "eeaaebaf01b4c3c59cce1df134cb7906e0f14695",
          "before": null
        },
        "src/jpip.rs": {
          "after": "7c606f6e89935d8a2a39cd6dfb3b41aa0769961a",
          "before": "fe9dc19363428ead8db33d641a4466e932ca3062"
        },
        "src/jpip/automatic_headers.rs": {
          "after": "f1278df2abdadc1debeaa6f7e61b90fdade18bd4",
          "before": null
        },
        "src/jpip/byte_io.rs": {
          "after": "3a57fb9a98c874ee806d3d2ec652ac72dcbab9d2",
          "before": null
        },
        "src/jpip/cache.rs": {
          "after": "040460e8e12e86a4d2270a12288dd05799277d4c",
          "before": null
        },
        "src/jpip/mapping.rs": {
          "after": "461080ce47b8d00501f16d11e6a4220490726158",
          "before": null
        },
        "src/jpip/message.rs": {
          "after": "bc9fe66ec47da2a42ebd3c97d00fe487dd54ed5d",
          "before": null
        },
        "src/jpip/precinct.rs": {
          "after": "bd579f5a2758d17067f6215e35584793cb9b530e",
          "before": null
        },
        "src/jpip/progression.rs": {
          "after": "ba236d27334bc02ec3a521440b9d6167f80ebfd8",
          "before": null
        },
        "src/jpip/ranges.rs": {
          "after": "e64c63f54665bc93cfe12826b34b7d2a49ffe59c",
          "before": null
        },
        "src/jpip/reconstruction.rs": {
          "after": "dc5ea68ee243e9408b916f1e8cd4fcd02fa5c426",
          "before": null
        },
        "src/jpip/tests.rs": {
          "after": "fac210b2d11d4d3e844328a1909b95dcf167a809",
          "before": null
        },
        "src/jpx.rs": {
          "after": "295f4aee70be13f00546b2eeed3ab8dcc71a9f05",
          "before": "40aae4c7c85e890e54adc3811001db36d16aca65"
        },
        "src/jpx/channels.rs": {
          "after": "058a762b540d81999c76825a76452557e97ddf24",
          "before": null
        },
        "src/jpx/chroma.rs": {
          "after": "4d983031ef6d2db9f5aaff31f99abec101b6f64d",
          "before": null
        },
        "src/jpx/compositing.rs": {
          "after": "813d215815b833b37b312a5a3ba226674340eec5",
          "before": null
        },
        "src/jpx/inspection.rs": {
          "after": "f95813c0c433f2122f1b1060675a99d83dd4a445",
          "before": null
        },
        "src/jpx/layer_decode.rs": {
          "after": "bd06c54a4ff4a6a0995d0a62aae453f49c713b33",
          "before": null
        },
        "src/jpx/opacity.rs": {
          "after": "0ab4806a4655db3bd7b728fa9109fd6317f52b5a",
          "before": null
        },
        "src/jpx/proof_support.rs": {
          "after": "99283ff3f457adf27bfba929922330c22a2d27c1",
          "before": null
        },
        "src/jpx/registration.rs": {
          "after": "95c460f8f854095dfb1b6fe7ca94ae806d414249",
          "before": null
        },
        "src/jpx/render.rs": {
          "after": "7f900a5f13d586835473f0d6cd5c88c84e91ec7a",
          "before": null
        },
        "src/jpx/resources.rs": {
          "after": "98fc119c260e1bfd75ce160eea6e4a0a02c8f027",
          "before": null
        },
        "src/jpx/tests.rs": {
          "after": "6c59da1b77e710b5aec9db60ce80049eda72e6a6",
          "before": null
        },
        "src/jpx/timeline.rs": {
          "after": "55230bfdb70c13176f08979b24573e6acaff7e10",
          "before": null
        },
        "src/packet.rs": {
          "after": "f46ea91984e33440af9a8a2b49a42f9822189963",
          "before": "c9267c3ebb6471e753b370867ff02c03751902e0"
        },
        "src/packet/bit_reader.rs": {
          "after": "af36362bdbee55454bdcf99c3089a62a4be3118a",
          "before": null
        },
        "src/packet/body.rs": {
          "after": "da6df6553b88237953b13864a5279a87cf6ed6cc",
          "before": null
        },
        "src/packet/contributions.rs": {
          "after": "190c282e79991afa338b9c4d76a72bd0c91c4e20",
          "before": null
        },
        "src/packet/errors.rs": {
          "after": "171fc51fe7e85ed94effa469b2c351563750dabc",
          "before": null
        },
        "src/packet/multi_packet.rs": {
          "after": "f2ef39247d56ad3c3fb6e8fc4bf8e40d1a4ae7d4",
          "before": null
        },
        "src/packet/precinct.rs": {
          "after": "a3f7bbbe989df4e1e7b65c1a1bf8f17a76679de8",
          "before": null
        },
        "src/packet/progression.rs": {
          "after": "f1c673a6c992f22f471285a9b78dc736d8c114af",
          "before": null
        },
        "src/packet/proof_support.rs": {
          "after": "69602f637380d8f2b058abedfbc5ddcb127f0fdd",
          "before": null
        },
        "src/packet/tag_tree.rs": {
          "after": "efa95c3d6018a16b0cc1acf69cb258f3a329af52",
          "before": null
        },
        "src/packet/tests.rs": {
          "after": "844e2cdf24a6e18bccee4218412275a2979d4582",
          "before": null
        },
        "src/packet/tile.rs": {
          "after": "0d5e0087ce2b11c3850774fb076ac440c8bc469f",
          "before": null
        },
        "src/refinement.rs": {
          "after": "9496eb81ac909cf00db286f456c569e51910f037",
          "before": "d50daa8a3ccd0e3a47596036a0eddb8015f5fac7"
        },
        "src/refinement/composition.rs": {
          "after": "cf70382cb55461288d2c7ebdce94ab96281a3023",
          "before": null
        },
        "src/refinement/geometry.rs": {
          "after": "1dc7b2f7c3b411fc418b19f30568e460791996e5",
          "before": null
        },
        "src/refinement/headers.rs": {
          "after": "29a320e13300465fe6cd523979723e31ed87ba37",
          "before": null
        },
        "src/refinement/jpip.rs": {
          "after": "fb2d4079c735dc18f3d83a6bdc7fb3857b2b365c",
          "before": null
        },
        "src/refinement/packet.rs": {
          "after": "1691f261374c33a99dc9aa4900f1d630c72603a2",
          "before": null
        },
        "src/refinement/reconstruction.rs": {
          "after": "73f83a27bee29e77baa0e28f11ddc0f4b5932914",
          "before": null
        },
        "src/refinement/tier1.rs": {
          "after": "afaab8a13337291d6563545fc123ce63e3bc5131",
          "before": null
        },
        "src/tier1.rs": {
          "after": "9098108bc9b228c1bc5e18f255f1511ec827c097",
          "before": "be2b059c31a5b0db4571d8fc61e506c01fa69a47"
        },
        "src/tier1/coding.rs": {
          "after": "97db0665a7db39b90392d4b0c5eafcbc42452d43",
          "before": null
        },
        "src/tier1/contributions.rs": {
          "after": "95cb48b1541c5456869d473719d49a0e2ed475c5",
          "before": null
        },
        "src/tier1/ht_cleanup.rs": {
          "after": "706c921f738e38bea8d05ff1af69929e632c927d",
          "before": null
        },
        "src/tier1/ht_cleanup_readers.rs": {
          "after": "9168f3eb0021a45f4980675293ea16be092754fb",
          "before": null
        },
        "src/tier1/ht_contributions.rs": {
          "after": "7dbf3749c8bafcc46778b517fd432562ef7c4fd4",
          "before": null
        },
        "src/tier1/ht_metadata.rs": {
          "after": "8c1627baa08b4af60c901209bc04ed6bfe817d09",
          "before": null
        },
        "src/tier1/ht_refinement.rs": {
          "after": "626a9e4c8c6bf4e69763651ebd1604e6566edfed",
          "before": null
        },
        "src/tier1/ht_refinement_readers.rs": {
          "after": "69e4d372dfa6064eff1e3f28cb1d1fd0e4dbe194",
          "before": null
        },
        "src/tier1/ht_segments.rs": {
          "after": "173e7693739a7c7cb2c4bf2472a1c581033cd680",
          "before": null
        },
        "src/tier1/legacy_passes.rs": {
          "after": "2b1efd4cff8ba2eb931bb1a8e541dd1f7fc74fc3",
          "before": null
        },
        "src/tier1/legacy_segments.rs": {
          "after": "71b839c389ccbab77ee5add44f87d166ac6fea24",
          "before": null
        },
        "src/tier1/proof_support.rs": {
          "after": "4678daf49e72303f78188b9b003722c2b860ddae",
          "before": null
        },
        "src/tier1/raw.rs": {
          "after": "09aeaf52d624f12cb5675340ecd099ef88eba1f6",
          "before": null
        },
        "src/tier1/state.rs": {
          "after": "a618c3bfddbac107f2664147c4c41af9c08edc15",
          "before": null
        },
        "src/transform.rs": {
          "after": "17dfd06fd603cc74a73a7d72adb6e20ca2f2902c",
          "before": "52bcb12ebdc177b96d310ceed1f04968c22ae2e7"
        },
        "src/transform/arbitrary.rs": {
          "after": "d2d98682456dc638e8b94f6febca8407bcf3874d",
          "before": null
        },
        "src/transform/arithmetic.rs": {
          "after": "084d59bc21121bc049c364cdf83489aad7a6f741",
          "before": null
        },
        "src/transform/coefficients.rs": {
          "after": "f62b872d66bd83293bde312785f8c70bb043a464",
          "before": null
        },
        "src/transform/geometry.rs": {
          "after": "77f3d5051d79c5a7d854cc73fb63fd83fda84060",
          "before": null
        },
        "src/transform/levels.rs": {
          "after": "91687a26556a8148ece2b7658c46113bc883ced1",
          "before": null
        },
        "src/transform/output.rs": {
          "after": "ffcad2e7ae98328448ec2dad9ce58a9aae2ad73a",
          "before": null
        },
        "src/transform/proof_support.rs": {
          "after": "cce0c36b594ccc62a9798095cb0f33cfeaed9715",
          "before": null
        },
        "src/transform/quantization.rs": {
          "after": "4330666515d0fe35c4235a1d5a163e3ec3a75b23",
          "before": null
        },
        "src/transform/tests.rs": {
          "after": "f7cc5a205332f45e90151bb14a74352c55292171",
          "before": null
        },
        "src/transform/wavelets.rs": {
          "after": "843eee6378858bad4494edf3c4bb5e0dc7e329d6",
          "before": null
        },
        "validation/expected-package-files.txt": {
          "after": "75b8ae8a0f0edf530ec711a73ba26fb45d291a64",
          "before": "dad10d65b8755dab328cd6e969ef022ece8b5328"
        },
        "validation/framework.py": {
          "after": "c883a6694c1e06e9c604734bf8adf4ed36899e2a",
          "before": "868da3d7b50f1a022de8306e822557d2eaaaeff8"
        },
        "validation/normative-coverage.json": {
          "after": "f474916d1a8c073f16e17e692459674ee770fd22",
          "before": "53f1b409b3910b26147979bbbf142cbe256dd18c"
        },
        "validation/tests/test_framework.py": {
          "after": "988bfe0a7c7b39dbac2be6e171786b102ca3cfe1",
          "before": "ac92b5cd896d92a9634b8def13d61b4cb47a0956"
        }
      }
    },
    {
      "id": "proposal-193-packet-metadata",
      "profile": "packet-metadata-finalization",
      "source_pr": 193,
      "source_head": "3eb0b67849d3f36428179bc03841ea552d08333d",
      "ci_run": 41084399839,
      "verus_run": 41084400145,
      "rationale": "Complete source-derived raw packet sum and metadata finalizers with exact errors, reader/borrow frames, verified recursive sum, and strict binding regressions; no normative correspondence or source-integration approval.",
      "paths": {
        "specs/packet_input.rs": {
          "before": "759a249a7b8075e8364dba02b2af5b7aceb3221d",
          "after": "e2d981fc32cecdb456b9c9fe7f1dc6ff7f0e9947"
        },
        "src/codestream/packet_headers.rs": {
          "before": "fb96f69f20bbe0e053c1b35860ec238f4c39816c",
          "after": "e4e05266f7f0a9146c9df0e735ffb388560bfb4a"
        },
        "src/codestream/proof_support.rs": {
          "before": "4a67d35f42dead523b857799582cab86e9bbb8d3",
          "after": "909b70c57267fc8592e09ec1aaaef7d0ead9f59c"
        },
        "src/codestream/tests.rs": {
          "before": "9317d9d81f43fb8d8d382e2a5733d8583789afc2",
          "after": "76292936a11333af0afdd8570dfd3aeffda3f16a"
        },
        "src/error.rs": {
          "before": "c901da343f5b8cebccca3e3808ae1aa5de5ccca0",
          "after": "56ff1537775b82c7eab0f256f3704334d07796ee"
        },
        "validation/framework.py": {
          "before": "c883a6694c1e06e9c604734bf8adf4ed36899e2a",
          "after": "6f888c3afec04104ffea27d7c307a3a43afb497c"
        },
        "validation/normative-coverage.json": {
          "before": "f474916d1a8c073f16e17e692459674ee770fd22",
          "after": "ea8103d583f0b2dba9a64ac62bdfdc347f234c87"
        },
        "validation/tests/test_framework.py": {
          "before": "988bfe0a7c7b39dbac2be6e171786b102ca3cfe1",
          "after": "e260337c210b0c1b7ab0d959b9fd6eebb630cea0"
        }
      }
    },
    {
      "id": "proposal-195-component-style-cache",
      "profile": "tile-component-style-cache",
      "source_pr": 195,
      "source_head": "e25716fce02bb0f50f56681a30a3621842cc4ef8",
      "ci_run": 41110257458,
      "verus_run": 41110257409,
      "rationale": "Replace duplicate dense component-style snapshots by indices into retained payload owners; prove actual payload identity and latest-owner/absence invariants, preserving persistence, errors and outputs. Eligibility only, not source integration, a universal resource bound, normative correspondence or publication approval.",
      "paths": {
        "src/codestream/layout.rs": {
          "before": "c91fb9df1748eaf10ae768f3e8c14db7b5e4d6a9",
          "after": "bf51820d4ff7fb07a08f778f4930b01cec47a09a"
        },
        "src/codestream/tiles.rs": {
          "before": "567f93406ade6a5c50af705d54b8cba899318c88",
          "after": "52cb94617dc7a25420ec332b6646b62a54f2f258"
        },
        "src/codestream/tests.rs": {
          "before": "76292936a11333af0afdd8570dfd3aeffda3f16a",
          "after": "d8b26c92471551d87c57b555fca21644bd02b0cd"
        }
      }
    },
    {
      "id": "proposal-197-tile-packet-admission",
      "profile": "tile-packet-admission",
      "source_pr": 197,
      "source_head": "dad4c56a09013e623fea1cbf95c4e6d0b675326e",
      "ci_run": 41135383976,
      "verus_run": 41135383979,
      "rationale": "Complete actual PLT/PPT admission results and reader/counter frames with unchanged error and partial-commit order, real producer joins and strict regressions on the accepted cache base. Eligibility only, not source integration, outer parser composition or normative certification.",
      "paths": {
        "src/codestream/tiles.rs": {
          "before": "52cb94617dc7a25420ec332b6646b62a54f2f258",
          "after": "8507fac5449134d6de3d312abf25a47cfcc08cc5"
        },
        "src/codestream/packet_headers.rs": {
          "before": "e4e05266f7f0a9146c9df0e735ffb388560bfb4a",
          "after": "0d1bcedbeb1e133e5e8d3e1db07846894f063204"
        },
        "src/codestream/tests.rs": {
          "before": "d8b26c92471551d87c57b555fca21644bd02b0cd",
          "after": "04674a4d307721f62f297c1cf50f3d8aae6c948d"
        },
        "specs/packet_input.rs": {
          "before": "e2d981fc32cecdb456b9c9fe7f1dc6ff7f0e9947",
          "after": "b6059efda674f7744b65fe8515ffe3e1a6c614a2"
        },
        "validation/framework.py": {
          "before": "6f888c3afec04104ffea27d7c307a3a43afb497c",
          "after": "130956f39e2bc0df1f697552e884964ffe3f4c5f"
        },
        "validation/normative-coverage.json": {
          "before": "ea8103d583f0b2dba9a64ac62bdfdc347f234c87",
          "after": "efe35f0c9fcd27bfef93f30ada3eed642eb29d44"
        },
        "validation/tests/test_framework.py": {
          "before": "e260337c210b0c1b7ab0d959b9fd6eebb630cea0",
          "after": "b8bef762be5ce1630b79964d58986ce43833116a"
        }
      }
    },
    {
      "id": "proposal-198-component-depth-registration",
      "profile": "component-depth-registration",
      "source_pr": 198,
      "source_head": "40d2711c808632170de1ed00a498f7390bb9db2e",
      "ci_run": 41144651127,
      "verus_run": 41144651097,
      "rationale": "Complete actual CBD/CRG application and physical uniformity with total raw-state results, exact prefix errors, flags, tails and reader frames; retain accepted packet requirements and strict real-producer regressions. Eligibility only, not source integration, outer composition or normative certification.",
      "paths": {
        "src/codestream/layout.rs": {
          "before": "bf51820d4ff7fb07a08f778f4930b01cec47a09a",
          "after": "3b6c15fdfb3530656d8c31d3380f4e90545f45c4"
        },
        "src/codestream/image_header.rs": {
          "before": "8097986505cb3648d8f286e5503cf2392010d825",
          "after": "4da02579c26b4a9d256dcb0fa33881ce9f4b359a"
        },
        "src/codestream/tests.rs": {
          "before": "04674a4d307721f62f297c1cf50f3d8aae6c948d",
          "after": "87f81b6b666e0158abf90e9979701808215fcfd7"
        },
        "specs/mod.rs": {
          "before": "75b6291ea1bbd43e57860303452f0e80790dabfa",
          "after": "dcd03b15ee413b334404f4a597d0bb6bd19eb594"
        },
        "validation/framework.py": {
          "before": "130956f39e2bc0df1f697552e884964ffe3f4c5f",
          "after": "88851b1a123dde18d527c10f35164e3775d03ca6"
        },
        "validation/normative-coverage.json": {
          "before": "efe35f0c9fcd27bfef93f30ada3eed642eb29d44",
          "after": "4f71439c38267c0c48e348a88e180cadd682e415"
        },
        "validation/tests/test_framework.py": {
          "before": "b8bef762be5ce1630b79964d58986ce43833116a",
          "after": "0f1269e3439de9ffd79b2bee610e9674dcb4f193"
        }
      }
    },
    {
      "id": "proposal-200-decomposition-resolution",
      "profile": "decomposition-resolution",
      "source_pr": 200,
      "source_head": "92d08756a49eddaca6a4e1d927e12374b53a0a31",
      "ci_run": 41153180810,
      "verus_run": 41153180822,
      "rationale": "Complete actual first-match DFS/ADS lookup, style setter and ordered owner resolution with source-derived raw results, exact error order, partial commits, tails and parser frames; preserve accepted component/packet/cache producers and strict regressions. Eligibility only, not source integration, outer composition or normative certification.",
      "paths": {
        "src/codestream/decomposition.rs": {
          "before": "c1ce6dc3d16d14d636719790e9b5e8bcbe1851c9",
          "after": "fe9e6748ad146d88088e8a0384a5f8edb309101d"
        },
        "src/codestream/extensions.rs": {
          "before": "f016e820bab1d68e265da480e090f43f28ab5a51",
          "after": "e42d80f187e7b428852410de4f8b291f2e53e48b"
        },
        "src/codestream/coding_style.rs": {
          "before": "9b19da5edabff4faeff7475b9c88f18e1be2ad55",
          "after": "d937e2e20ac3bb15b06ea5c031d436cf20e53d90"
        },
        "src/codestream/proof_support.rs": {
          "before": "909b70c57267fc8592e09ec1aaaef7d0ead9f59c",
          "after": "aed8844b95b495da27add74d8c804e1c946adf5d"
        },
        "src/codestream/tests.rs": {
          "before": "87f81b6b666e0158abf90e9979701808215fcfd7",
          "after": "5e7547b86070596dd64a38b90297ced7b4c2aaed"
        },
        "specs/mod.rs": {
          "before": "dcd03b15ee413b334404f4a597d0bb6bd19eb594",
          "after": "9ef8b6a88ee07594c83e68629f1d59735725462b"
        },
        "validation/framework.py": {
          "before": "88851b1a123dde18d527c10f35164e3775d03ca6",
          "after": "3ae67cfe274b84e8169ad97113a95199fdcf9cd5"
        },
        "validation/normative-coverage.json": {
          "before": "4f71439c38267c0c48e348a88e180cadd682e415",
          "after": "8469e4fd72db58d19d71fabf3b2d8d181764abfb"
        },
        "validation/tests/test_framework.py": {
          "before": "0f1269e3439de9ffd79b2bee610e9674dcb4f193",
          "after": "e31370e9ca7f27ae54f80b39fa1ac97f23d556af"
        }
      }
    },
    {
      "id": "proposal-202-sot-reader-marker",
      "profile": "sot-reader-marker",
      "source_pr": 202,
      "source_head": "30102aad867548e6f07907f2db099f1072583650",
      "ci_run": 41252094188,
      "verus_run": 41252094124,
      "rationale": "Complete actual SOT Result and parser frame with source-derived exact marker-admission predicates, raw header fields, preserved error precedence and segment-reader partial commits. Existing models, pins, admission sets and caps unchanged. Eligibility only, not source integration, lifetime, normative or publication approval.",
      "paths": {
        "src/codestream/reader.rs": {
          "before": "ebad4a7821322e99dfeeabed632b213ca8f2b4c2",
          "after": "919bb9b17339dd840baea88a9db938e557dea11c"
        },
        "src/codestream/tiles.rs": {
          "before": "8507fac5449134d6de3d312abf25a47cfcc08cc5",
          "after": "f8c2abf6108357ff18816823f47f45c078fb0d48"
        },
        "src/codestream/proof_support.rs": {
          "before": "aed8844b95b495da27add74d8c804e1c946adf5d",
          "after": "6d50a37e0fb7c8b4ef622bb07e6594fe7955873a"
        },
        "src/codestream/tests.rs": {
          "before": "5e7547b86070596dd64a38b90297ced7b4c2aaed",
          "after": "aba72932ab810a90463c9795e642dd55a8cbfd6f"
        },
        "specs/mod.rs": {
          "before": "9ef8b6a88ee07594c83e68629f1d59735725462b",
          "after": "8ae9fac97ff55d537da1a4c765dc0721a619f93e"
        },
        "validation/framework.py": {
          "before": "3ae67cfe274b84e8169ad97113a95199fdcf9cd5",
          "after": "8bbb5258e27a611a4a0a29926113d7d4d1cdbf93"
        },
        "validation/normative-coverage.json": {
          "before": "8469e4fd72db58d19d71fabf3b2d8d181764abfb",
          "after": "5e0befd4bd0b07be56823da34f0c207956b12180"
        },
        "validation/tests/test_framework.py": {
          "before": "e31370e9ca7f27ae54f80b39fa1ac97f23d556af",
          "after": "4c22aed6faff81a3ad5852769b2fd63c798efa05"
        }
      }
    },
    {
      "id": "proposal-206-tile-data-window",
      "profile": "tile-data-window",
      "source_pr": 206,
      "source_head": "58d4c50c5c97f8002fc1e686694ffad9641b1403",
      "ci_run": 41261831548,
      "verus_run": 41261831538,
      "rationale": "Complete actual tile-data range Result and reader frame with unchanged zero-length early and fixed-length late cursor commits around packet metadata finalizers, raw range/error precedence and exact source-derived packet-input model. Existing SOT and other model meanings, controller policy, pins and caps unchanged. Eligibility only, not source, lifetime, normative or publication approval.",
      "paths": {
        "src/codestream/tiles.rs": {
          "before": "f8c2abf6108357ff18816823f47f45c078fb0d48",
          "after": "2ce7ec064bb79bedd57c435deb200f3abad09d38"
        },
        "src/codestream/proof_support.rs": {
          "before": "6d50a37e0fb7c8b4ef622bb07e6594fe7955873a",
          "after": "e1a38ee2d1a8293798e259d9886afe52157106e4"
        },
        "src/codestream/tests.rs": {
          "before": "aba72932ab810a90463c9795e642dd55a8cbfd6f",
          "after": "51fe581f07aca7d2096b1c0186e71486c8dbbdfc"
        },
        "specs/packet_input.rs": {
          "before": "b6059efda674f7744b65fe8515ffe3e1a6c614a2",
          "after": "e16a50ea7f2125be54627dafa92630252770b59e"
        },
        "validation/framework.py": {
          "before": "8bbb5258e27a611a4a0a29926113d7d4d1cdbf93",
          "after": "528b8af4b7640c81ad7a86b84cf018ca54eb4635"
        },
        "validation/normative-coverage.json": {
          "before": "5e0befd4bd0b07be56823da34f0c207956b12180",
          "after": "d89f0ca3362e4f6c521b6788d2b9ec4ccdd5b531"
        },
        "validation/tests/test_framework.py": {
          "before": "4c22aed6faff81a3ad5852769b2fd63c798efa05",
          "after": "93adbc2e5f1b1ec5c125908f16103c750081a1a7"
        }
      }
    },
    {
      "id": "proposal-208-main-component-finalization",
      "profile": "main-component-finalization",
      "source_pr": 208,
      "source_head": "adeaaa3b0129c4f5030222384c210cf25c22f950",
      "ci_run": 41362592419,
      "verus_run": 41362592321,
      "rationale": "Complete actual main component coding-style and quantization finalizers with raw owner lookup, ordered partial updates, full Result and parser frames. Accepted window and other model meanings, controller policy, pins and caps unchanged. Eligibility only, not source integration, lifetime, normative or publication approval.",
      "paths": {
        "src/codestream/layout.rs": {
          "before": "3b6c15fdfb3530656d8c31d3380f4e90545f45c4",
          "after": "601e2f4aa4ea4535b6ea99f89955f9751b1c6276"
        },
        "src/codestream/coding_style.rs": {
          "before": "d937e2e20ac3bb15b06ea5c031d436cf20e53d90",
          "after": "fccfe422fe1e8b67f19158e85466591b2c724857"
        },
        "src/codestream/quantization.rs": {
          "before": "b2ed1bd063706a17623b64a5352cc7362423cbf5",
          "after": "aacf491e8622863ef6c946b284ee465a6d7b3f6e"
        },
        "src/codestream/proof_support.rs": {
          "before": "e1a38ee2d1a8293798e259d9886afe52157106e4",
          "after": "ec6aea6c4654c9270f6ccd95c7a5e13779ef479c"
        },
        "src/codestream/tests.rs": {
          "before": "51fe581f07aca7d2096b1c0186e71486c8dbbdfc",
          "after": "523ab6a1c5ab8aa8a3ade68f9821da367c803502"
        },
        "specs/mod.rs": {
          "before": "8ae9fac97ff55d537da1a4c765dc0721a619f93e",
          "after": "5a927ed5abd33f663c4e1f41921e54b3caf9fffc"
        },
        "validation/framework.py": {
          "before": "528b8af4b7640c81ad7a86b84cf018ca54eb4635",
          "after": "e695a610abf9cc967f9de63c9a5ac1104742cb81"
        },
        "validation/normative-coverage.json": {
          "before": "d89f0ca3362e4f6c521b6788d2b9ec4ccdd5b531",
          "after": "bcacd075ee0e1c91eb18bd508c0b35fac3a4fc7a"
        },
        "validation/tests/test_framework.py": {
          "before": "93adbc2e5f1b1ec5c125908f16103c750081a1a7",
          "after": "d0b1c2c78e27e4f62bc9fc10fa76f238cd2354ce"
        }
      }
    },
    {
      "id": "proposal-210-layout-prologue",
      "profile": "layout-prologue",
      "source_pr": 210,
      "source_head": "91df2b0537d024d91f4fffd6d35458b41b9bb2d0",
      "ci_run": 41370207229,
      "verus_run": 41370207276,
      "rationale": "Complete actual raw SOC/segment/SIZ prologue Result, image fields, header start and reader frame through the real layout caller. Existing finalizers, window, model meanings and requirement reference unions, controller policy, pins and caps unchanged. Eligibility only, not source integration, lifetime, normative or publication approval.",
      "paths": {
        "src/codestream/layout.rs": {
          "before": "601e2f4aa4ea4535b6ea99f89955f9751b1c6276",
          "after": "3cf79541364cf877e803f9b1a6b0db0b64bfdb47"
        },
        "src/codestream/proof_support.rs": {
          "before": "ec6aea6c4654c9270f6ccd95c7a5e13779ef479c",
          "after": "52424a594d8eed1af903f82e77918b741ed779f8"
        },
        "src/codestream/tests.rs": {
          "before": "523ab6a1c5ab8aa8a3ade68f9821da367c803502",
          "after": "176bbabf80bc807eb4299f6e2fde7ecd91d9f99c"
        },
        "specs/layout_input.rs": {
          "before": null,
          "after": "dc8e5eae0ad7827077d704027b356e9883df9a89"
        },
        "specs/mod.rs": {
          "before": "5a927ed5abd33f663c4e1f41921e54b3caf9fffc",
          "after": "89aa88cf4bddeb555f71a4acb614f973b18b5369"
        },
        "validation/framework.py": {
          "before": "e695a610abf9cc967f9de63c9a5ac1104742cb81",
          "after": "7f98828e2ec8a185551d71aab93b310b74c34de1"
        },
        "validation/normative-coverage.json": {
          "before": "bcacd075ee0e1c91eb18bd508c0b35fac3a4fc7a",
          "after": "f88050a00d57d3964f3f184692cbffceb3ac70b8"
        },
        "validation/tests/test_framework.py": {
          "before": "d0b1c2c78e27e4f62bc9fc10fa76f238cd2354ce",
          "after": "e1c0f76af75fa7e576111f8c0caacfe51d893ff1"
        },
        "validation/expected-package-files.txt": {
          "before": "75b8ae8a0f0edf530ec711a73ba26fb45d291a64",
          "after": "b71fac7e12e563eb3ca44808853b5cd81fc51a6e"
        }
      }
    }
  ]
}
```
