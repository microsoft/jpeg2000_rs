# Uncovered performance candidates evaluation

Date: 2026-11-24. Report branch: `perf/eval-report`.
Decoder baseline: `54abff44a778b6c210d580770286a531370550b6` (refreshed `origin/main`).

**Status: coverage verified; measurements in progress.** The initial blocked
report is preserved in commit `ee94a76`. GitHub CLI authentication and local
build/profiling capability are now restored. No completed A-G qualification or
speedup is claimed by this checkpoint.

## Executive summary

The supplied provisional matrix is materially outdated. Current trackers
#469-#483 cover most of its proposed storage, HT, wavelet, color and threading
work. This evaluation must not duplicate those investigations, including ones
closed with a negative result.

The remaining evaluation focuses on context-table specialization, the distinct
floating-point/whole-plane representation alternatives, untracked accounting
and inlining work, intra-tile region pruning, and missing benchmark/ISA
qualification. Existing code already prunes discarded-resolution entropy
execution; that half of C11 is not a new optimization.

No measured go recommendation or issue draft exists yet. Prototype branches
are isolated, unmerged, and cut from the recorded default-branch baseline.
The original `openjpeg-compat` checkout remains untouched.

## Step 0: verified coverage

Authenticated exports contain **91 issues, 392 PRs and 357 remote branch
heads**. All **89 keyword-matching issue bodies** and **375 keyword-matching
PR bodies** were read completely. The other records did not match the supplied
keyword scan. Issues #440, #446-#449, #453-#456, #132, #289 and #299 and PRs
#450-#452 were read in full. Additional closure comments for #446-#449 were
checked, distinguishing stale pre-merge prose from exported current state.
The exports are session evidence, not new GitHub issues.

The default fetch refspec tracks only `main`; `git ls-remote --heads origin`
was therefore used for a complete branch export. An empty local `*perf*`
remote-tracking query is **not** absence evidence.

Merged, open/in-flight, and explicitly negative completed investigations all
count as tracked scope. A closed-unmerged historical prototype is not a
delivered implementation. Quotations below establish scope, not independently
reproduced performance.

| Candidate | Verdict and covering work | Exact remaining scope | Quoted scope evidence |
|---|---|---|---|
| H | Partly covered: #419/#420, #450/#452, #487; #485-#491 in flight | Reuse infrastructure; establish this prompt's pinned, equivalent-output, in-memory matrix and missing corpus/profile coverage | #487: “not a matched OpenJPEG/consumer comparison” |
| C1-HT | **Covered by #474**; adjacent #414/#416/#457 | Skip narrow HT coefficient-owner work | #474: “Evaluate a private narrow-primary owner for HT and retained compact legacy state” |
| C2 | Partly covered: #447/#457, #16, #415/#416 | Table-driven context derivation and explicit stripe/block-size specialization beyond existing incremental flags | #457: “incrementally updating neighbor flags”; #415: “No mutable significance cache” |
| C3 | **Covered by #448**, completed negatively | Skip another MQ loop investigation; do not reintroduce discarded MPS/renormalization changes | #448: “Only if the profile supports further changes, isolate one candidate at a time” |
| C4-97 | Partly covered: #433/#434, #446/#451, #471/#473, #436 | Floating-point/whole-plane narrowing alternatives only; not shipped bounded products, row-wise layout, or tracked residual SIMD | #433: “Q16 products with signed 32-bit operands”; #473: “bounded narrower lanes with widening products” |
| C5 | Partly covered: #431/#432, #451, #477/#479/#480 | Any genuinely additional whole-plane i32 or complete output-stage fusion, not preparation/placement fusion or tracked row kernels/owner moves | #451: “without signed-magnitude/quantized staging owners”; #480: “Validate congruent MCT slices once” |
| C6 | **Covered by #482** | Skip bounded decoder parallelism | #482: “keeping deterministic single-thread default and avoiding mandatory dependencies” |
| C7 | Partly covered: #289/#359; narrow field batching #472/#485 | General amortized accounting beyond HT field batching, with exact budget/error frontiers and documented cooperative granularity | #485: “full counter/work increments are admissible”; #289: “not … a hard wall-clock guarantee” |
| C8 | Partly covered: #470/#471/#476/#477/#480; #421/#422 replay reuse excluded | Only scratch reuse not already subsumed by those owner/row/metadata changes; inspect actual residual reach first | #471: “Start with a reusable row scratch”; #348: “cancelled spectral-scratch attempt is NOT included” |
| C9-ISA | Partly covered: #449/#450, #487 | Explicit x86-64-v3/AVX2 and matched OpenJPEG ISA qualification, not another native-consumer tuning study | #450: “Portable defaults stay unchanged”; no x86-64-v3 profile in the exported PR bodies |
| C10 | **Covered by #472**, with #485 in flight | Skip bulk HT reservoirs; existing VLC table is not missing | #472: “Reverse VLC peek walks a copied cursor”; “A VLC table already exists” |
| C11 | Partly covered: #469/#481, #368/#369; source already skips discarded-resolution entropy | Intra-selected-tile ROI code-block/filter-support pruning only | #469: “avoid coefficient allocation for discarded resolutions”; #368: “avoids allocating for every image tile in a small ROI” |
| C12 | Partly covered: #290, #248/#269, #417/#418, #223 | Broader hot-function inlining and runtime-check audit; do not call ghost code runtime overhead | #269: “ZERO removed/added normalized bodies”; “not full production cfg/erasure/lifetime qualification” |

### Additional idea

**X1: saved-entropy continuation for repeated incremental input.** #349 delivers
buffered/replay input, not saved entropy state. This is distinct from already
tracked terminal-prefix/replay reduction #475 and full-input coalescing
discussed in #421. It needs an independently scoped state/error/limit model and
an interactive-feed workload before any go recommendation.

### Important corrections to the supplied hypotheses

- #453-#456 are compatibility/routing/adjudication issues, not new performance
  candidates.
- #299 is a **historical bounded investigation with unresolved independent
  numerical correctness**, not current-main parity or a universal max-one
  conformance tolerance. Its four supplied irreversible controls are still
  required numerical comparisons for any 9/7 change.
- #289 promises cooperative checkpoints, not hard preemption; the default
  proof profile does not verify its optional clock/TLS effects.
- Current `TypedImage` output is planar 64-bit samples, not an 8/16-bit
  interleaved buffer. The benchmark converts OpenJPEG to that actual standard
  output representation inside its primary timed interval.
- A “checked word” HT accumulator does not mean compact coefficient backing
  or a 64-bit buffered directional bit reader.
- Earlier experimental wavelet paths #427-#430 were subsequently removed by
  #433/#434. They are not current production implementations.

## Step 1: machine, builds and harness

The shell is native Linux aarch64 on Microsoft Azure Linux 3.0. CPU information
reports implementer `0x41`, part `0xd49`, corresponding to Neoverse-N2.
Allowed CPUs are 0-31; timing is pinned to CPU 3. This is a shared host:
wall-clock results are indicative, and no global governor/turbo settings
were changed.

- Rust 1.93.1, commit `01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf`,
  LLVM 21.1.8; existing installed toolchain exposed explicitly.
- Session-local Zig 0.14.1 / Clang 19.1.7 provides C compilation and the Rust
  system linker. Its wrapper selects `aarch64-linux-gnu`, generic CPU.
- Session-local CMake 4.4.5 and Ninja 1.13.2; no host packages installed.
- OpenJPEG v2.5.4, commit
  `6c4a29b00211eb0430fa0e5e890f1ce5c80f409f`, built static, CMake Release,
  O3, debug symbols and `-ffp-contract=off` for **both correctness and timing**.
- Generic Cargo release; consumer ThinLTO/cgu1; native consumer configuration.
  Baseline/native C flags match the ISA choice. No fast-math or runtime ISA
  dispatch was introduced.
- Vendor RPM signatures and metadata checksums verified for session-local perf
  and Valgrind. User-space hardware instructions/cycles were successfully
  exercised without changing kernel policy. The initial missing-tool status
  is resolved, not a remaining blocker.

The unpublished [harness](../../tools/bench-vs-openjpeg/README.md) reuses the
existing frozen first-party MIT cohort, recipes and provenance. It reads each
raw codestream once, creates a fresh decoder per iteration, and excludes file
I/O, output serialization and result destruction from the measured interval.
The primary output is Rust's actual typed planar 64-bit buffer; OpenJPEG's
32-bit output is converted to the same representation while timed. Its native
output is measured separately.

Default protocol: three warmups; at least fifteen iterations **and** two
seconds of summed decode time per process; two fresh-process rounds with
reversed backend order; medians and IQRs. Per-process wait4 metrics retain max
RSS, faults and CPU time, not allocation counts. All inputs are hashed.
Lossless results must agree with the reference and the authored source.

The available baseline covers eight synthetic 1MP legacy streams (smooth/noisy,
gray/RGB, lossless/lossy) and three synthetic HT streams. **It does not
qualify complete classes A-G.** Natural/12-24MP/12-16-bit, coding-mode,
structural, 8K-window and official conformance coverage remain explicit gaps.
No native x86-64 runner is attached; x86-64-v3/AVX2 results cannot be inferred
from this aarch64 host.

Baseline and stage-share tables will be populated only from completed runs.

## Step 2: candidate checkpoint

| ID | Current disposition | Branch / next evidence |
|---|---|---|
| H | Measurements in progress | `tools/bench-vs-openjpeg`; no speed recommendation yet |
| C1-HT | Covered by #474; skipped | No duplicate prototype |
| C2 | Context-LUT prototype prepared; unqualified | `perf/eval-c2-context-lut`; tests, paired timing and Verus still required |
| C3 | Covered by #448; skipped | Existing negative investigation is not an unlimited no-future-gain claim |
| C4-97 | Needs more data on uncovered alternatives | No changed 9/7 implementation or numerical claim |
| C5 | Needs more data on genuinely additional fusion | First separate tracked preparation/color/ownership scope |
| C6 | Covered by #482; skipped | No new threading knob |
| C7 | Needs more data | Exact charges/error states must not be replaced with speculative upper-bound success |
| C8 | Needs residual source/profile evidence | Do not duplicate #471 row scratch or #476 metadata streaming |
| C9-ISA | ARM measurements in progress; x86 unmeasured | No inferred AVX2 result |
| C10 | Covered by #472; skipped | No duplicate HT reader |
| C11 | Reduction pruning already implemented; ROI remainder | Source: `src/packet/tile.rs` selects entropy execution by resolution |
| C12 | Inlining-only prototype prepared; unqualified | `perf/eval-c12-mq-inline`; no arithmetic/check/proof removal |
| X1 | Needs more data | Saved entropy is a distinct, high-risk optional coordinator change |

No prototype is a production recommendation. In particular, unchanged native
samples do not substitute for Verus verification, cross-target determinism or
the requested conformance corpus.

## Combined result and remaining gates

No go stack, ranking, or issue drafts are justified at this checkpoint.
No GitHub issue or PR has been filed and no branch merged or released.
Full corpus, stage-share, paired prototype, numerical, proof and determinism
evidence remain to be collected; missing cells will stay explicitly unmeasured
rather than be filled with historical issue numbers.

## Completed first-pass experiment: C2 count-to-context lookup

This section records the completed first pass. A full rerun with explicit
output-consumption barriers before both end timestamps is in progress; the
first-pass evidence remains preserved rather than being overwritten.

- **Coverage:** remainder of #447/#457. This is only branchy count-to-context
  mapping, **not** stripe-packed flags, flag-mask-to-context lookup, or
  32/64-block specialization.
- **Hypothesis:** partly confirmed.
  [The current mapping](../../src/tier1/state.rs#L213) branches over neighbor
  counts; the compact path already maintains incremental neighbor flags.
- **Stage share:** sampled generic Tier-1 shared/legacy self time spans
  48.41-66.63% on A/B inputs. This broad parent bucket includes ownership and
  pass work, not an isolated context timer or a strict wall-time ceiling.
- **Prototype:** `perf/eval-c2-context-lut`, `edd777d`; 57 inserted/7 removed
  lines, including a focused count-class/orientation test. A const-generated
  128-byte table preserves every public count class via saturation and a
  masked in-range index. It does not change coefficient storage.
- **Correctness:** all 22 image/configuration dumps exactly match paired
  controls. The decoder's default all-target suite passes 1,383 library and
  six example tests on both Rust 1.93.1 and actual MSRV 1.88.0; five doctests
  pass on each version. Seven focused cooperative-deadline controls pass
  with MSRV. Four original #299 irreversible controls remain max 1 with
  2/85/5/322 differing samples before and after; both reversible controls
  remain exact. Cross-target execution is not tested.
- **Verification:** **not run**, not a theorem failure. Local `cargo verus`
  is absent, the pinned workflow requires x86, and prototype push was denied
  HTTP 403 to `telecos`, preventing exact-ref workflow dispatch. No proof,
  contract, check, verifier pin or resource policy was removed.
- **Effort/risk:** S native prototype; M proof follow-through; medium
  maintenance risk. Stripe representation/block specialization remains L
  and is not evaluated by this small experiment.
- **Recommendation:** **needs more data for C2 overall; do not adopt this
  lookup on the legacy evidence.** Intended A/B cases do not improve. The
  generic HT signal is not enough for adoption: it does not repeat under
  the consumer profile, and whole-process HT instructions increase rather
  than decrease. Broader stripe/block work is still unmeasured.

Positive change means slower; these are class geometric means of paired
per-image after/before medians, not historical issue timings.

| Class subset | Generic change | Consumer change |
|---|---:|---:|
| A | +0.665% | +0.741% |
| B | +0.523% | +0.273% |
| E | -3.680% | -0.366% |

Generic noisy-lossless gray/RGB instructions rise 1.667%/1.667%;
HT instructions rise 0.170-0.182%. The apparent generic HT time improvement
is therefore retained as an unexplained signal, **not attributed as a
context-kernel win**. Per-case medians, IQR/noise decisions and all controls
are in [the first-pass table](data/c2-summary.csv).

## Completed first-pass experiment: C12 MQ inlining hints

The same definitive rerun caveat applies to these preserved first-pass results.

- **Coverage:** remainder beyond #290/#248/#269 and the already tracked HT
  reader inlining. This is not a new MQ algorithm or a repeat of discarded
  early-MPS/renormalization experiments from #448.
- **Hypothesis:** ghost/spec/proof bodies are already
  [cfg-excluded](../../src/lib.rs#L77) in ordinary execution. Runtime
  arithmetic/resource checks are functional error behavior, not presumed
  proof-only overhead. The measured experiment only exposes four existing
  [MQ helpers](../../src/mq.rs#L564) to cross-unit inlining.
- **Stage share:** generic noisy-lossless gray/RGB samples attribute
  37.35%/34.94% to standalone MQ symbols. This is not the share of function-call
  overhead or work accounting alone.
- **Prototype:** `perf/eval-c12-mq-inline`, `aa1e5ba`; four `#[inline]`
  attributes, with no arithmetic, state, checks or proof-contract changes.
- **Correctness:** 22 paired dumps are exact; #299 statistics remain
  max 1 with 2/85/5/322 differing irreversible samples and exact reversible
  controls. Both Rust versions pass 1,382 default library tests, six example
  tests and five doctests; seven MSRV deadline controls pass. Cross-target
  execution remains untested.
- **Verification:** not run for the same missing local verifier / denied
  prototype-push reasons. No passing baseline proof receipt is substituted.
- **Effort/risk:** S; low native semantic risk, but fresh verification is
  still required for any retained source.
- **Recommendation:** **no-go for retaining these measured hints.** Intended
  legacy gains are within noise and no targeted-stage gain is established.
  This does not reject every possible DWT/output inlining experiment or
  authorize removing guards under stronger, unproved caller assumptions.

| Class subset | Generic change | Consumer change |
|---|---:|---:|
| A | -0.136% | +0.055% |
| B | +0.560% | -0.112% |
| E | -0.686% | -0.098% |

Noisy-lossless gray/RGB whole-process user instructions decrease only
0.244%/0.238%. Generic executable `.text` shrinks 496 bytes; consumer `.text`
shrinks 16 bytes, not a whole-ELF/debug-information claim.
See [per-case initial results](data/c12-summary.csv).

## C4-97: uncovered floating-point / representation alternatives

- **Coverage:** #433/#434 already provide bounded signed-32-bit operand
  multiplication; #451 supplies row-wise layout, and #473 tracks residual
  fixed-Q16/narrow-lane vectorization. None is a missing new C4 prototype.
- **Hypothesis:** partly false. [The present fixed multiply](../../src/transform/wavelets.rs#L410)
  has an unchecked-within-proved-bounds product plus the original checked
  fallback. It is not uniformly a checked wide multiply. The separate
  generic row-wise 5/3 loop demonstrably emits NEON `add .2d` and `ssra .2d`;
  this does not establish vectorized 9/7 or AVX2.
- **Stage share / ceiling:** first-pass generic B DWT self shares are
  17.41-18.31%, versus much larger Tier-1 work. Removing all DWT cannot
  recover more than its sampled CPU portion; these whole-process samples
  are not exact decode-wall-time bounds.
- **Prototype:** none for the uncovered float/whole-plane representation.
  Preserving the public centered-Q16 reconstruction API while retaining
  float values through MCT/output needs a new range, rounding and refinement
  argument, not only different lifting constants.
- **Correctness:** no 9/7 source change; no float before/after statistics
  exist. The supplied #299 controls were replayed for the actual C2/C12
  changes, not substituted for an unbuilt float experiment. Native 16-bit,
  signed, high-precision and cross-target qualification is still missing.
- **Verification:** no C4 source/proof changed. Exact-source verifier access
  is blocked; existing integer contracts are not asserted to prove a float
  pipeline. Its pinned-tool support has not been qualified.
- **Effort/risk:** L/high, especially public reconstruction headroom,
  numeric fallback boundaries and independently unresolved #299/#187 rules.
- **Recommendation:** **needs more data**. First restore proof execution,
  qualify representative precision/geometry inputs, and keep the already
  tracked integer/SIMD work separate. No unmeasured float speedup is claimed.

## C5: genuinely additional whole-plane kernels and fusion

- **Coverage:** preparation/dequantization/placement fusion is already
  implemented by #451. [Its fast path](../../src/decode/reconstruction/fused.rs#L301)
  preflights then writes directly, retaining the checked staging fallback.
  #477/#479 cover native/container ownership and #480 covers MCT/color row
  kernels. None should be re-proposed as missing work.
- **Hypothesis:** partly confirmed. [Standard component arithmetic](../../src/image/component_transform.rs#L95)
  and [typed rounding/level shift](../../src/image/arithmetic.rs#L24) still
  use checked i64 values. The public typed result remains 64-bit regardless
  of a possible narrower internal representation.
- **Stage share / ceiling:** first-pass B dequant/placement samples span
  4.10-6.80%; typed output 1.31-1.33%; standard RGB MCT 0.83-0.95%.
  These buckets do not establish that all their work can disappear, and
  broader plane narrowing also overlaps DWT/memory traffic.
- **Prototype:** none for an additional complete i32/fused pipeline.
  Admission must follow actual coefficient/intermediate bounds, not nominal
  8/16-bit output depth. Widening back to the unchanged public format must
  remain inside the measured work.
- **Correctness/verification:** no C5 source or proof changed. New precision,
  ROI, generic-transform, error-order and refusal-boundary evidence is
  missing. Exact-source verifier execution is blocked; existing #451 proofs
  do not prove a different internal plane type.
- **Effort/risk:** L/medium-high; representation relations and first-error
  semantics span multiple stages.
- **Recommendation:** **needs more data**. Separate any genuinely additional
  pipeline from the tracked row/ownership work, profile the remaining passes
  on high-precision inputs, and obtain range/proof qualification before
  introducing a second internal arithmetic representation.

## C7: exact work accounting versus unsafe coarse precharging

- **Coverage:** #289/#359 establish cooperative checkpoint semantics;
  #472/#485 already cover exact admissible HT field batching. General
  amortized accounting remains outside that narrower work.
- **Hypothesis:** partly confirmed. [MQ decisions](../../src/mq.rs#L564)
  and renormalization shifts call [the exact counter](../../src/mq.rs#L755).
  There is **no per-decision deadline-clock read** in this function to remove.
  Native deadline checkpoints are separately gated.
- **Stage share / ceiling:** first-pass standalone MQ samples range
  3.91-37.35% across A/B. Work charging is only an unisolated subset; assigning
  the entire MQ share to accounting would be false attribution.
- **Prototype:** none. Precharging a conservative pass maximum as observed
  work would change tight-budget failures and partial/error states. A viable
  experiment needs an admissible-bound fast path with exact final charges,
  exact fallback near frontiers, and bounds covering actual pass/style work.
- **Correctness/verification:** no accounting or checkpoint changed; the
  measured C2/C12 branches preserve these calls and pass deadline controls.
  No new overshoot bound or wall-clock SLA was measured. Exact-state proof
  execution is currently blocked, so no coarsened policy is presented as safe.
- **Effort/risk:** M-L/high, including termination, malformed-prefix state,
  overflow, precise work refusal and cancellation granularity.
- **Recommendation:** **needs more data**. Isolate real accounting cost
  before implementation, derive/check the bound, and verify exact budget/error
  behavior rather than replacing checks with `debug_assert!`.
