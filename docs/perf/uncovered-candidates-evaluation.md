# Uncovered performance candidates evaluation

Execution: 24-25 November 2026. Branch: `perf/eval-report`.
Decoder baseline: `54abff44a778b6c210d580770286a531370550b6` (`origin/main` at start).

**Status: measured partial evaluation, not the full definition of done.**
Coverage is verified, an available ARM64 matrix is reproducible, and two
isolated experiments were tested and measured. Other uncovered mechanisms have
explicit needs-more-data cards. C12 now passes exact-source/package Verus;
C2 fails pinned Verus compilation and stays rejected. Native x86-64/v3,
cross-target execution and the full A-G corpus remain unqualified.

## Executive summary

- The provisional uncovered list was outdated: #469-#483 already track most
  proposed ownership, HT, wavelet, color and threading work.
- Rust is **not faster than OpenJPEG** on any measured class subset.
  Generic one-core geometric-mean Rust/OpenJPEG ratios are **4.8739 A,
  6.4183 B and 8.8275 E**. These are synthetic subsets, not complete classes.
- A bounded count-to-context LUT and four MQ inlining hints provide no
  retention-worthy repeatable gain. Neither is recommended for adoption.
  A first-pass apparent HT gain from the LUT did not replicate.
- No go stack or go-issue drafts exist. No issue, PR, merge, release-branch
  change, tag or publication was performed.
- Both prototypes are committed on local, unmerged branches cut from the
  recorded default branch. The report branch changes no decoder runtime,
  model, proof, root manifest or root lockfile.

The original `openjpeg-compat` checkout was not used for edits or switched.
The initial authentication-blocked report remains in `ee94a76`; coverage,
harness and individual candidate checkpoints are separately committed.

## 1. Verified coverage gate

Authenticated exports contain **91 issues, 392 PRs and 357 remote heads**.
All **89 matching issue bodies** and **375 matching PR bodies** were read in
full. Required issues #440, #446-#449, #453-#456, #132/#289/#299 and PRs
#450-#452 were read completely. Selected closure comments were also checked.
Exported state takes precedence over stale pre-merge prose.

The configured fetch refspec tracks only `main`; `git ls-remote --heads origin`
provided the complete branch export. An empty local `*perf*` query was not
treated as absence evidence. Merged, in-flight and completed-negative
investigations count as tracked scope; closed-unmerged historical code is not
treated as a shipped implementation.

Quotations establish **coverage**, not independently reproduced historical
performance. Raw exports accompany the session evidence.

| ID | Coverage and trackers | Exact remaining scope | Quoted evidence |
|---|---|---|---|
| H | Partly: #419/#420, #450/#452, #487; #485-#491 in flight | Reuse infrastructure; establish this prompt's matched-output/ISA/thread/corpus matrix | #487: “not a matched OpenJPEG/consumer comparison” |
| C1-HT | **Covered by #474**; adjacent #414/#416/#457 | Skip narrow HT coefficient-owner work | #474: “Evaluate a private narrow-primary owner for HT and retained compact legacy state” |
| C2 | Partly: #447/#457, #16, #415/#416 | Direct flag/context tables and stripe/block specialization beyond existing flags | #457: “incrementally updating neighbor flags”; #415: “No mutable significance cache” |
| C3 | **Covered by #448**, completed negatively | Skip another MQ algorithm investigation | #448: “Only if the profile supports further changes, isolate one candidate at a time” |
| C4-97 | Partly: #433/#434, #446/#451, #471/#473, #436 | Float/whole-plane representation alternatives, not existing bounded products/layout/tracked SIMD | #433: “Q16 products with signed 32-bit operands”; #473: “bounded narrower lanes with widening products” |
| C5 | Partly: #431/#432, #451, #477/#479/#480 | Additional whole-plane i32/complete fusion, not preparation/placement, row kernels or owner moves | #451: “without signed-magnitude/quantized staging owners”; #480: “Validate congruent MCT slices once” |
| C6 | **Covered by #482** | Skip bounded parallelism | #482: “keeping deterministic single-thread default and avoiding mandatory dependencies” |
| C7 | Partly: #289/#359; narrow batching #472/#485 | General exact amortized accounting beyond HT fields | #485: “full counter/work increments are admissible”; #289: “not … a hard wall-clock guarantee” |
| C8 | Partly: #470/#471/#476/#477/#480; replay #421/#422 excluded | Residual reuse beyond those owner/row/metadata changes | #471: “Start with a reusable row scratch”; #348: “cancelled spectral-scratch attempt is NOT included” |
| C9-ISA | Partly: #449/#450, #487 | Explicit x86-64-v3/AVX2 and matched OpenJPEG ISA qualification | #450: “Portable defaults stay unchanged”; no explicit v3 profile in exported PR bodies |
| C10 | **Covered by #472**, #485 in flight | Skip bulk directional readers; existing VLC table is not missing | #472: “Reverse VLC peek walks a copied cursor”; “A VLC table already exists” |
| C11 | Partly: #469/#481, #368/#369; source already prunes discarded entropy | Intra-selected-tile ROI block/filter-support pruning only | #469: “avoid coefficient allocation for discarded resolutions”; #368: “avoids allocating for every image tile in a small ROI” |
| C12 | Partly: #290, #248/#269, #417/#418, #223 | Broader runtime-check/codegen/inlining audit | #269: “ZERO removed/added normalized bodies”; “not full production cfg/erasure/lifetime qualification” |
| X1 | Uncovered saved-entropy mechanism beyond #349 | Interactive entropy continuation, not buffered snapshots or #475 terminal replay | #291: “buffered/replay with explicit EOF, not saved entropy” |

Important corrections:

- #453-#456 are compatibility/routing/adjudication issues, not new performance
  ideas.
- #299 is a historical bounded numerical investigation with an unresolved
  independent correctness verdict, not current-main parity or a universal
  conformance tolerance. Its supplied controls were replayed here.
- Checked-word HT payload accumulation is not narrow coefficient backing or a
  buffered directional reader.
- Experimental wavelets #427-#430 were subsequently removed by #433/#434.
- Ordinary proof/spec bodies are cfg-excluded. Functional checked arithmetic
  must not be relabelled removable proof overhead.

## 2. Machine, flags and method

Native Microsoft Azure Linux 3.0, aarch64; CPU implementer `0x41`, part `0xd49`
(Neoverse-N2). Allowed CPUs: 0-31. Timed children use CPU 3; owned compilation
uses at most two CPUs/jobs. **Shared host: wall times are indicative.**
No governor, turbo, kernel policy or global package settings were changed.

| Item | Recorded configuration |
|---|---|
| Rust | 1.93.1, `01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf`, LLVM 21.1.8 |
| MSRV validation | Actual Rust 1.88.0, `6b00bc388`; session-local installation |
| C/linker | Session-local Zig 0.14.1 / Clang 19.1.7, GNU ARM64 target |
| Reference | Static OpenJPEG v2.5.4, `6c4a29b00211eb0430fa0e5e890f1ce5c80f409f` |
| CMake/Ninja | Session-local 4.4.5 / 1.13.2 |
| C flags | CMake Release; `-O3 -DNDEBUG -g -ffp-contract=off` |
| Generic | Cargo release/O3, debug 1, default LTO/codegen units; generic C CPU |
| Consumer | Rust ThinLTO, one codegen unit; C remains matched generic Release |
| Native | Consumer Rust plus `-C target-cpu=native`; C plus `-mcpu=native` |
| Profiling | Vendor-signed perf and Valgrind 3.22.0, installed only in session |

Generic C preprocessing actually reports ARMv8/NEON, and Rust target cfg reports
NEON. The ISA claim is not inferred only from flag names. No fast-math, nightly,
new runtime dependency, unsafe Rust or runtime kernel dispatch was introduced.
All C timing builds also use `-ffp-contract=off`.

### Equivalent output and lifecycle

The current raw API returns `TypedImage`: planar unsigned `u64` or signed `i64`
samples, **not an 8/16-bit interleaved buffer**. The primary metric uses that
actual standard output. The C driver converts OpenJPEG's planar 32-bit samples
to matching 64-bit planes inside the interval. Separate C native-output timing
omits conversion; Rust's measured native typed output is already its primary
output. Centered fractional reconstruction is not substituted for typed output.

Each program reads compressed bytes once and creates a fresh decoder per
iteration. Setup/header/decode/end-decompress, output allocation/conversion and
internal cleanup are timed. Input I/O, output dumps/comparison, result
destruction and CSV writes are excluded. Both completed outputs pass an
optimization barrier before the end timestamp.

Three warmups; **at least 15 iterations AND two seconds summed decode time**
per process; two fresh-process rounds with reversed backend order. Tables give
medians and inclusive IQRs. Candidate changes inside combined IQRs are noise.
Profiles and counters are collected separately from uninstrumented timing.

**Reference correction:** OpenJPEG's constructor honors `OPJ_NUM_THREADS`,
while `opj_codec_set_threads` destroys/replaces that pool. The authoritative
head-to-head run uses constructor `OPJ_NUM_THREADS=0`, then the API sets one
worker. This avoids redundant worker creation. Every timed receipt records
`OPJ_NUM_THREADS=0`, `BENCH_OPENJPEG_THREADS=1`. Both execution threads remain
on the same one-CPU budget. Earlier reference timings are retained as
diagnostics, not mixed into the tables below.

Rust prototype pairs use unchanged, hash-checked Rust binaries and do not link
OpenJPEG, so the reference lifecycle correction does not change those paired
experiments. #299 reference rasters were also unchanged.

### Corpus and qualification limits

Inputs reuse the repository's **first-party MIT** frozen bytes and recipes in
[consumer-tuning](../../validation/consumer-tuning/README.md):

- Eight 1024-square smooth/noisy gray/RGB, reversible/irreversible streams,
  with RGB MCT, deterministically extracted from the frozen JP2 files.
- Three synthetic OpenJPH 0.33.0 HT streams: 512-square gray lossless,
  768-square RGB lossless, 512-square RGB lossy. Encoder revision, arguments,
  source/input hashes and license are retained in the existing manifest.
- Six original #299 controls retrieved from the supplied v2 issue bundle,
  verified against ZIP SHA256
  `d5b6d432ee17616be33806a2163aeadcf2d20997f4724c602a4b11a603f3503d`.
- Supplemental discard 1/2/3 and 512-square windows on the 1024-square noisy
  gray lossless/lossy cases.

**Not collected/qualified:** natural-photo and 12-24MP/12-16-bit cohorts,
coding-mode class C, structure class D, 8K class F, official/external conformance
class G, complete HT families, native x86-64/v3, and 2/4/8-thread scaling.
Repository tests are not relabelled official conformance. The available classes
below are explicitly subsets. Broader corpus collection is remaining work,
not an invented licensing or tool-availability failure.

## 3. Baseline results

Ratio is Rust time / OpenJPEG time; below 1.0 is faster.
Each cell is a geometric mean of per-image median ratios.

| Configuration | A subset primary / native-output | B subset primary / native-output | E subset primary / native-output |
|---|---:|---:|---:|
| Generic | 4.8739 / 5.1064 | 6.4183 / 6.8543 | 8.8275 / 9.6571 |
| Consumer | 4.9048 / 5.1294 | 6.1555 / 6.5834 | 8.4491 / 9.2626 |
| Native | 4.8081 / 5.0210 | 6.0771 / 6.5382 | 9.0783 / 10.0723 |

The below-one goal is **not met in A, B or E subsets**. It is not established
for C/D/F/G. Native tuning is not a universal improvement.

Generic primary per-image examples:

| Image | Rust median (IQR), ms | OpenJPEG median (IQR), ms | Ratio |
|---|---:|---:|---:|
| Smooth gray 5/3 | 105.8612 (1.3380) | 11.9220 (0.0768) | 8.8795 |
| Noisy gray 5/3 | 329.0390 (1.3007) | 105.3079 (0.1467) | 3.1245 |
| Noisy RGB 5/3 | 977.7327 (1.4234) | 327.5112 (0.5869) | 2.9853 |
| Smooth RGB 9/7 | 303.3496 (5.0257) | 45.1602 (0.4161) | 6.7172 |
| Noisy RGB 9/7 | 278.4925 (1.8172) | 55.2309 (0.5287) | 5.0423 |
| HT RGB lossless | 197.3492 (2.0497) | 20.9944 (0.1095) | 9.4001 |

All images, three builds and both C output modes are in
[baseline-summary.csv](data/baseline-summary.csv).
The authoritative head-to-head run contains **20,747** timed observations;
prototype pairs add **1,932 C2 / 1,940 C12**, and supplemental selections
**42,025**, totaling **66,644** uninstrumented timing records.

### Sampled stage shares and gain bounds

Fixed-period user-cycle sampling avoids under-sampling OpenJPEG's short-lived
worker threads. Buckets are **leaf/self attribution**, not isolated stage
timers. Inlined work can be charged to callers; unknown TCD self time remains
unresolved. Profiles include startup/destruction and exclude kernel cycles,
unlike the precise decode interval. Use them as planning estimates, **not
mathematically strict wall-time speedup ceilings**.

Rust share ranges over images in each subset:

| Subset | MQ | Tier-1 shared/legacy | HT | DWT | Dequant/placement | MCT | Typed/output | Alloc/copy/zero |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| A | 10.77-36.63% | 56.65-66.37% | -- | 1.82-7.32% | 2.12-5.68% | 0-0.27% | 0.29-1.21% | 0.40-1.80% |
| B | 4.14-11.38% | 49.04-61.77% | -- | 17.22-18.72% | 4.86-6.86% | 0-1.07% | 1.35-1.67% | 2.17-7.40% |
| E | -- | 11.24-11.72% | 50.59-60.16% | 6.87-16.60% | 6.26-8.06% | 0-0.58% | 0.87-1.19% | 4.17-4.42% |

Shared Tier-1 includes owner/state work even on HT, not evidence that HT uses
legacy MQ. Context derivation and work accounting are not isolated percentages.
Both backends' complete per-image attribution is in [stages.csv](data/stages.csv).

Three fresh counting processes per backend/image retain cycles, instructions,
IPC inputs, branches/misses and L1 misses. **LLC-load-misses is unsupported**;
it remains explicit, not zero. Example whole-process noisy RGB lossless:

| Backend | User instructions | User cycles | IPC | Branch misses | L1 data-load misses |
|---|---:|---:|---:|---:|---:|
| Rust | 9,463,935,441 | 3,220,675,906 | 2.9385 | 62,709,605 | 10,818,288 |
| OpenJPEG | 1,504,175,342 | 1,084,691,399 | 1.3867 | 42,602,759 | 9,008,691 |

These include startup/input, not just entropy. See [counters.csv](data/counters.csv).

### Memory and allocation

Generic peak process RSS, KiB, from the two typed-output timing processes:

| Image | Rust | OpenJPEG |
|---|---:|---:|
| Noisy gray lossless | 89,076 | 62,288 |
| Noisy RGB lossless | 222,772 | 128,216 |
| HT RGB lossless | 223,692 | 128,244 |

All profiles/modes and faults/CPU observations are in
[resources.csv](data/resources.csv). RSS is not live heap or allocation count.

Separate DHAT, one smooth-gray decode, no warmup:

| Backend | Heap blocks | Total allocated bytes | Live bytes at global peak |
|---|---:|---:|---:|
| Rust | 4,607 | 204,881,162 | 87,293,754 |
| OpenJPEG | 1,466 | 12,969,359 | 12,897,603 |

This includes process/input/output work. It does not attribute every byte to
untracked scratch. DHAT also confirms the C equivalent-output allocation
receives **8,388,608 bytes of writes**, not merely an unused allocation.

## 4. Correctness and verification

- Six lossless corpus images recover their independent authored source
  hashes in all three configurations: 18 source checks.
- Every one of the 11 images preserves each backend's own complete dump/hash
  across generic, consumer and native builds.
- Each prototype's 22 image/configuration dumps exactly matches its control.
  No checksum-only inner timing loop replaces output creation.
- Both libraries' lossless/lossy windows exactly match their own full-decode
  crops in all four unit-sampling checks.
- Broader five-image irreversible baseline differences are at most one,
  with full counts retained; this is not a new conformance tolerance.

Original #299 controls, baseline -> C2 -> C12, same in generic/consumer:

| Control | Max absolute difference | Differing samples |
|---|---|---|
| Gray reversible | 0 -> 0 -> 0 | 0 -> 0 -> 0 |
| RGB reversible | 0 -> 0 -> 0 | 0 -> 0 -> 0 |
| Gray 9/7 rate 1 | 1 -> 1 -> 1 | 2 -> 2 -> 2 |
| Gray 9/7 rate 4 | 1 -> 1 -> 1 | 85 -> 85 -> 85 |
| RGB 9/7 rate 1 | 1 -> 1 -> 1 | 5 -> 5 -> 5 |
| RGB 9/7 rate 4 | 1 -> 1 -> 1 | 322 -> 322 -> 322 |

Input hashes and individual comparisons:
[299-statistics.csv](data/299-statistics.csv).
This replay does not settle #299/#187's independent normative questions.

| Validation | C2 | C12 |
|---|---:|---:|
| Rust 1.93.1 default library tests | 1,383 pass | 1,382 pass |
| Actual Rust 1.88.0 default library tests | 1,383 pass | 1,382 pass |
| Example tests, each compiler | 6 pass | 6 pass |
| Doctests, each compiler | 5 pass | 5 pass |
| Focused MSRV cooperative-deadline controls | 7 pass | 7 pass |

These are decoder default all-target suites, not all optional-feature/workspace
or official conformance qualification. The harness also passes six Python
regressions, strict Clippy, formatting and C `-Wall -Wextra -Werror` checks;
its actual MSRV build passes. Four invalid-window controls and exact full/window
output checks pass. Package enumeration verifies tooling/report data are absent
from the 417-file decoder package.

**24-November snapshot: Verus not run, not a theorem failure.** `cargo verus` is unavailable locally;
the pinned job uses an x86 binary/Rust 1.98.1. Attempted exact prototype push
was denied HTTP 403 to `telecos`, so no exact-ref workflow was dispatched.
The user was unavailable to grant write/JIT access. No alternative identity,
pin change, proof deletion or baseline-receipt substitution was used.
The prototypes must remain unqualified until an authorized exact-source run.
Cross-target/thread-count execution is likewise not asserted.

## 5. Candidate cards

Class tables below aggregate per-image medians geometrically; positive change
means slower. Detailed per-image IQR/noise decisions remain in CSV. Derived
Rust/OpenJPEG ratios use the separately paired, lifecycle-corrected reference,
not a simultaneous prototype C run. Only within-prototype paired changes are
used to claim candidate effects.

### H: matched benchmark harness

- **Coverage:** partial reuse of existing comparison work.
- **Hypothesis/evidence:** the existing native revision driver was not the
  requested complete OpenJPEG matrix; actual typed output is planar 64-bit.
  The new [unpublished harness](../../tools/bench-vs-openjpeg/README.md)
  reuses frozen corpus generation/provenance and times matching output.
- **Measured:** baseline, counters, stage estimates, RSS, DHAT and selections
  above; no decoder optimization or attributable speed gain.
- **Correctness:** source oracles, full dumps, #299, barriers and lifecycle
  verified. Proofs not affected by tooling; cross-target/full corpus missing.
- **Effort/risk:** M/low decoder risk.
- **Recommendation:** **needs more data for full H qualification**. The
  available subset is runnable, but complete A-G is not delivered as measured.

### C9-ISA: parity and code generation

- **Coverage:** #449/#450 already cover consumer tuning; explicit v3 remains.
- **Evidence:** generic NEON was checked in actual compiler definitions.
  Emitted `transform::rowwise::lift_rows` contains `add v0.2d` and
  `ssra v2.2d, ..., #1` within the lifting loop, not merely Q-register copies.
  This does not establish 9/7 vectorization or AVX2.
- **Measured:** three native ARM64 configurations above, with unchanged
  outputs. Build commands/flags and process receipts are retained.
- **Prototype:** build/tooling only; no library dispatch or default profile
  change. Verification not affected.
- **Effort/risk:** S additional matrix work/low; native artifacts nonportable.
- **Recommendation:** **needs more data on x86-64/v3**. CI should retain a
  portable baseline plus matched consumer builds on each architecture;
  document native tuning as optional, not a universal default win. Add
  explicit v3/codegen qualification on an appropriate runner before claiming
  AVX2 or ISA-tier benefits.

### C1-HT: narrow HT coefficient owners

**Covered by #474; skipped.** Checked-word payload arithmetic is not narrow
backing. No duplicate prototype, test/proof receipt or new speed recommendation.
The HT baseline supports the existing tracker, not a measured storage gain.

### C2: context tables, flags and block specialization

- **Coverage:** remainder beyond #447/#457's existing incremental flags.
- **Hypothesis:** [count-to-context mapping](../../src/tier1/state.rs#L213)
  is branchy. A direct packed-flag lookup is a different, larger experiment.
- **Parent stage share:** Tier-1 shared/legacy 49.04-66.37% on A/B; not an
  isolated context timer or strict end-to-end ceiling.
- **Prototype:** `perf/eval-c2-context-lut`, `edd777d`, 57 inserted/7 removed
  lines including a focused count-class/orientation test. A const-generated
  128-byte table preserves public count classes via saturation and a masked
  index. No stripe representation, block specialization or new storage.
- **Correctness:** all paired dumps/#299 exact as above; native/MSRV suites
  pass. The later exact-source Verus attempt rejects the const-table initializer
  (Section 8); cross-target prototype execution remains untested.
- **Effort/risk:** S native, M proof follow-through/medium.
- **Recommendation:** **no-go for this bounded count-LUT experiment**;
  **needs more data for the larger C2 remainder**. No class reaches a
  repeatable gain gate. The first-pass apparent generic HT improvement
  disappears on replication; it is not counted as a win.

| Subset | Config | Before ms | After ms | Change | Rust/OpenJPEG before -> after |
|---|---|---:|---:|---:|---|
| A | Generic | 316.1050 | 317.9104 | +0.5712% | 4.9308 -> 4.9589 |
| B | Generic | 169.7537 | 169.7828 | +0.0171% | 6.5112 -> 6.5123 |
| E | Generic | 82.5642 | 82.8406 | +0.3347% | 9.1374 -> 9.1680 |
| A | Consumer | 315.7843 | 318.8278 | +0.9638% | 4.9314 -> 4.9789 |
| B | Consumer | 161.7794 | 162.2135 | +0.2683% | 6.1939 -> 6.2106 |
| E | Consumer | 80.1266 | 80.0105 | -0.1450% | 8.8281 -> 8.8153 |

Noisy-lossless gray/RGB user instructions rise 1.667%/1.667%. Direct flag
lookup without count formation/clamping and 32/64 specialization were **not**
tested or disproved. See [c2-summary.csv](data/c2-summary.csv) and
[instructions.csv](data/instructions.csv).

### C3: MQ arithmetic hot loop

**Covered by completed #448; skipped.** No early-MPS, renormalization,
sentinel or state-table rewrite was reintroduced. Current noisy-input MQ share
is material; the historical negative investigation is not an unlimited
no-future-gain theorem. C7 accounting and C12 hints are separately scoped.

### C4-97: uncovered 9/7 representation alternatives

- **Coverage:** bounded signed-32 operand products already exist in
  [fixed_mul](../../src/transform/wavelets.rs#L410); layout and residual
  integer/SIMD work belong to #451/#473. Those parts are not new prototypes.
- **Hypothesis:** partly false: the current path is not uniformly a checked
  wide multiply. The public centered reconstruction API retains Q16 i64.
- **Stage share/ceiling:** B DWT 17.22-18.72% sampled user cycles; eliminating
  that stage alone cannot remove the much larger Tier-1 work. This is not a
  strict wall-time bound.
- **Prototype:** none for float/whole-plane alternatives. Keeping float
  through MCT/output while preserving reconstruction headroom/API and
  fallback semantics needs a new range/rounding/refinement argument.
- **Correctness/verification:** no C4 source/proof changed; no float
  before/after statistics exist. #299 controls are not substituted for an
  unbuilt float experiment. Native 16-bit/cross-target evidence and pinned
  float-proof support are unqualified; exact-source verification is blocked.
- **Effort/risk:** L/high.
- **Recommendation:** **needs more data**, coordinating #299/#187 and
  separating already tracked integer work. No unmeasured float gain claimed.

### C5: additional whole-plane kernels and fusion

- **Coverage:** [preflight/direct placement](../../src/decode/reconstruction/fused.rs#L301)
  is already fused by #451; ownership/color row work belongs to
  #477/#479/#480.
- **Hypothesis:** partly confirmed: [component arithmetic](../../src/image/component_transform.rs#L95)
  and [typed rounding/level shift](../../src/image/arithmetic.rs#L24) remain
  checked i64. Changing internal lanes does not change the required public
  64-bit result format.
- **Stage shares:** B dequant/placement 4.86-6.86%, typed output 1.35-1.67%,
  standard RGB MCT 0.79-1.07%; broader plane narrowing overlaps DWT/memory.
  These buckets cannot simply be assumed removable.
- **Prototype:** none beyond tracked work. Admission must follow actual
  coded/intermediate ranges, not output bit depth.
- **Correctness/verification:** no C5 change. Precision, ROI, generic
  transforms and first-error/refusal equivalence remain unqualified; verifier
  access is blocked.
- **Effort/risk:** L/medium-high.
- **Recommendation:** **needs more data** on genuinely additional pipeline
  work, including widening/output cost and full precision-domain fallbacks.

### C6: multithreading

**Covered by #482; skipped.** No Rust worker API or default behavior changed.
Matched 2/4/8-thread scaling and four-thread stack data do not exist; one-core
results are not relabelled scaling evidence.

### C7: exact amortized work/deadline accounting

- **Coverage:** #289/#359 define cooperative semantics; #472/#485 cover
  narrower exact HT field batching.
- **Hypothesis:** partly confirmed. [MQ decisions](../../src/mq.rs#L564)
  and renormalization shifts call [the exact counter](../../src/mq.rs#L755).
  There is no per-decision deadline-clock read here to remove.
- **Stage share:** MQ 4.14-36.63% on A/B. Charging is only an unisolated
  subset; assigning all MQ time to accounting would be false attribution.
- **Prototype:** none. Conservative maximum precharging as observed work
  changes tight-budget/partial-error behavior. A viable fast path needs an
  admissible bound, exact final charges and exact near-frontier fallback.
- **Correctness/verification:** no checks/accounting changed. No new
  overshoot bound/SLA measured; unchanged deadline controls pass. Exact-state
  verification is blocked, so no coarse policy is presented as safe.
- **Effort/risk:** M-L/high, including all styles, overflow and cancellation.
- **Recommendation:** **needs more data**: isolate cost, derive/test bounds,
  preserve precise errors, and do not remove checks with `debug_assert!`.

### C8: genuinely residual scratch reuse

- **Coverage:** #470/#471/#476/#477/#480 already own major surfaces;
  #421/#422 replay reuse is excluded.
- **Hypothesis:** partly confirmed in
  [scalar column fallback](../../src/transform/levels.rs#L502), which owns
  destination/per-column results. That is not the shipped row-wise standard
  path; independent residual reach is not established by this corpus.
- **Stage share:** A/B alloc/copy/zero 0.40-7.40%. Inlined copying and
  page-fault/cache cost make this an invalid cap on all memory-reuse gains.
  DHAT above establishes volume, not untracked-scratch attribution.
- **Prototype:** none; no global scratch abstraction or cross-call cache.
- **Correctness/verification:** no lifetime/zeroing/refusal model changed.
  Complete overwrite, actual owner requests and error order require proof;
  phantom allocations or capacity assumptions from equal sequences are not
  acceptable. Verifier access is now restored, but no C7 prototype or new
  accounting proof has been qualified.
- **Effort/risk:** M/medium for a bounded residual kernel, L for a new
  cross-call decoder API.
- **Recommendation:** **needs more data** on representative high-precision/
  arbitrary-kernel residuals; prefer existing owner/copy investigations.

### C10: HT reservoirs/tables

**Covered by #472, with #485 in flight; skipped.** VLC tables already exist.
Payload word accumulation, field batching and a general directional reservoir
are distinct; no duplicate implementation or measured gain was invented.

### C11: intra-tile ROI; discard pruning already exists

- **Coverage:** #469 owners, #481 tile discovery, #368/#369 selected owners.
- **Hypothesis:** reduction half is false.
  [Resolution selection](../../src/packet/tile.rs#L600) gates
  [entropy execution](../../src/packet/body.rs#L221).
  [Selected-tile decoding](../../src/decode/execution.rs#L603) receives
  discard levels, not an intra-tile filter-support/block mask. Tile culling
  itself already exists.
- **Stage share:** noisy-gray MQ plus Tier-1 shared work exceeds 90% of
  sampled CPU. Only work outside correctly expanded support is removable;
  halo/work fractions are not measured.
- **Prototype:** none for new block/partial-DWT pruning.
- **Correctness/verification:** matched requests and four exact full/crop
  checks pass below. These are 1024-square unit-sampling inputs, **not 8K
  class F**. Support margins, origins, mixed resolutions, subsampling,
  malformed-outside-ROI policy and new selected-state proofs remain open.
- **Effort/risk:** L/high.
- **Recommendation:** **needs more data**; combine with #469 owner work,
  derive support and preserve selected/full equivalence before new pruning.

Supplemental generic primary timings; these are different requests, **not
an optimization before/after speedup**:

| Request | Gray stream | Rust ms | OpenJPEG ms | Ratio |
|---|---|---:|---:|---:|
| Discard 1 | Lossless | 92.0308 | 25.3772 | 3.6265 |
| Discard 1 | Lossy | 38.1104 | 4.2640 | 8.9377 |
| Discard 2 | Lossless | 32.8600 | 6.0290 | 5.4503 |
| Discard 2 | Lossy | 24.5563 | 1.1188 | 21.9482 |
| Discard 3 | Lossless | 20.0338 | 1.5003 | 13.3532 |
| Discard 3 | Lossy | 18.7509 | 0.3512 | 53.3906 |
| Window 128,128,512,512 | Lossless | 327.9635 | 61.3334 | 5.3472 |
| Window 128,128,512,512 | Lossy | 89.5766 | 7.9921 | 11.2081 |

IQRs/native output: [partial-summary.csv](data/partial-summary.csv).
Reduction already saves substantial entropy work. The window remains near
full-tile Rust cost, consistent with the source-confirmed intra-tile gap.

### C12: proof erasure and inlining

- **Coverage:** ordinary ghost separation and finite preservation audits
  already exist; broader hints remain distinct from #417's HT reader work.
- **Hypothesis:** [ghost bodies are cfg-excluded](../../src/lib.rs#L77).
  Runtime arithmetic/resource checks are functional error behavior, not
  presumed proof-only overhead.
- **Stage share:** noisy-lossless gray/RGB MQ 36.13%/36.63%, not the share
  of calls or accounting alone.
- **Prototype:** `perf/eval-c12-mq-inline`, `aa1e5ba`; four `#[inline]`
  hints, no arithmetic, state, checks or proof-contract changes.
- **Correctness:** exact dumps/#299; native/MSRV/deadline suites above pass.
  Later exact-source and package Verus each pass 6,328 obligations with zero
  errors under the existing lifetime-disabled boundary (Section 8).
  Cross-target prototype execution remains untested.
- **Effort/risk:** S/low native semantic risk, fresh verification still required.
- **Recommendation:** **no-go for these measured hints**. No repeatable
  retention-level end-to-end or isolated-stage gain is established. This
  does not reject every possible inlining experiment or authorize guard removal.

| Subset | Config | Before ms | After ms | Change | Rust/OpenJPEG before -> after |
|---|---|---:|---:|---:|---|
| A | Generic | 316.0708 | 315.4293 | -0.2030% | 4.9302 -> 4.9202 |
| B | Generic | 170.1357 | 170.1992 | +0.0373% | 6.5258 -> 6.5283 |
| E | Generic | 84.6934 | 84.0100 | -0.8069% | 9.3731 -> 9.2975 |
| A | Consumer | 316.6742 | 316.7103 | +0.0114% | 4.9453 -> 4.9458 |
| B | Consumer | 162.4889 | 162.5626 | +0.0453% | 6.2211 -> 6.2239 |
| E | Consumer | 78.3675 | 78.7124 | +0.4400% | 8.6343 -> 8.6723 |

Noisy-lossless gray/RGB user instructions fall only 0.244%/0.238%.
Generic `.text` shrinks 496 bytes; consumer `.text` shrinks 16 bytes.
This is not whole-ELF/debug-information shrink.
See [c12-summary.csv](data/c12-summary.csv) and
[text-sizes.csv](data/text-sizes.csv).

### X1: saved-entropy interactive continuation

- **Coverage/evidence:** uncovered mechanism beyond #349.
  [The coordinator](../../src/incremental.rs#L160) says `feed` never decodes;
  requested previews are buffered snapshots, not saved entropy continuation.
  This is not #475 terminal replay or existing no-advance JPIP suppression.
- **Stage share/ceiling:** unknown; default-feature timing does not exercise
  the optional coordinator. Feed-all/decode-once callers have no repeated
  entropy work to remove.
- **Prototype:** none. Naive continuation after virtual MQ end fill is not
  equivalent; real-byte checkpoints and correct context/coefficient rollback
  are prerequisites.
- **Correctness/verification:** unchanged source. New output/status/EOF,
  retry/limit/deadline equivalence is untested. Default proof receipts do not
  qualify the existing optional coordinator, much less new saved state.
- **Effort/risk:** L/high.
- **Recommendation:** **needs more data**: equal-preview interactive workload,
  replay measurements and a scoped continuation model first. Do not claim a
  default full-image gain by omitting observable previews or caching rasters.

## 6. Stack, ranking, implementation order and issue drafts

There are **no qualified go candidates**, so no `perf/eval-stack`, combined
speedup, four-thread stack ratio, or draft go issue is justified.
The current stack result is unchanged baseline, not an unmeasured composition.

Next investigation order, **not an adoption ranking**:

1. Complete remaining H/C9 corpus/ISA/evidence gates; exact-source proof
   attempts are now recorded (C12 passes, C2 fails and stays rejected).
2. Prefer existing #469/#470/#474 ownership and #472 reader investigations
   over duplicate global scratch work.
3. Investigate remaining intra-tile ROI with #469/geometry/error-policy
   prerequisites; source and matched requests show a real gap.
4. If continuing C2, test direct packed flags/block specialization on coding
   modes after representation invariants stabilize, not this slower count LUT.
5. Isolate C7 cost before deriving exact amortized guards. Further MQ work
   belongs with its existing tracker rather than a duplicate issue.
6. Additional C5 integer representation work needs range/error relations;
   C4 float work additionally needs precision/headroom and #299 reconciliation.
7. X1 requires an actual preview workload and continuation model.

No speculative expected percentage is substituted for measured gain.

## 7. Reproduction, persistence and blockers

Portable instructions and one-command runner:
[tools/bench-vs-openjpeg](../../tools/bench-vs-openjpeg/README.md).

```sh
bash tools/bench-vs-openjpeg/evaluate.sh FRESH_OUTPUT OPENJPEG_254_SOURCE \
  C2_WORKTREE C12_WORKTREE 3 ORIGINAL_NUMERICAL_299_DIRECTORY
```

In this session, the [restored-toolchain wrapper](../../../reproduce-evaluation.sh)
provides the exact local PATH/linker/profiler bindings:

```sh
bash /absolute/path/to/reproduce-evaluation.sh /absolute/fresh/output
```

It does not change system packages or require GitHub write access.
The optional #299 inputs are not silently replaced when absent.
Full commands, binary/compiler/input hashes, runtime thread receipts,
unmodified raw CSV and profile/counter/heap data remain in session evidence.
Compact measured tables in [data/](data/) are committed; raw data stays outside
the published crate. Local prototype refs can be transferred to an authorized
x86 verifier without merging them.

Corrected tooling attempts are preserved: initial missing tools/authentication,
Zig's rejected `-march=armv8-a` spelling (generic CPU wrapper used instead),
perf padding/IPC parsing, insufficient adaptive worker samples (fixed period
used), MCT/DWT symbol classification, CSV line endings, output-consumption
barriers, and redundant OpenJPEG pool setup. Failed or superseded runs are
not promoted into authoritative tables.

Remaining gates:

- [x] Coverage verified against current exported issues/PRs/branches.
- [x] Available matched ARM64 harness/corpus/baseline/profiles committed.
- [x] Every supplied candidate and additional X1 has an explicit disposition.
- [x] Two local experiments tested/measured; original #299 controls replayed.
- [x] Exact-source Verus attempted on both: C12 source/package pass; C2 const-table
  compilation fails and the prototype remains rejected (Section 8).
- [ ] Complete A-G corpus, isolated stage-wall timers and residual attribution.
- [ ] Native x86-64/v3/AVX2, cross-target determinism and missing precision cases.
- [ ] Remaining uncovered prototypes after proof/numerical/error prerequisites.

**The complete prompt's definition of done is not met.** This report uses its
explicit blocked-candidate reporting fallback, without fabricated measurements,
weakened proof/safety guarantees, or claims that missing cells passed.

## 8. Continuation on 25 November

The user enabled JIT at 08:51 UTC. At that time both the session GitHub CLI credential and
the repository's existing noninteractive Git credential still authenticate as
`telecos` with read access; repository API reports `push: false`, and the exact
two prototype refs still receive HTTP 403. No write permission or proof-workflow
success is inferred from host JIT activation. Corpus work continues separately.

At 09:55 UTC the user restored the expired JIT grant. A fresh API check then
reported `push: true`, and normal non-forced pushes of the unchanged C2/C12
prototype commits succeeded. Exact-source pinned Verus workflows were dispatched:

- C2 `edd777d27cedf56083a18a5a92e7725c1d460fff`:
  [run 45590181513](https://github.com/microsoft/jpeg2000_rs/actions/runs/45590181513).
  Failed at the module-only rejection guard; production/package verification
  was skipped. The compiler rejects the new `ZERO_CONTEXTS` initializer:
  `zero_context_table` has exec mode and cannot be called there
  (`src/tier1/state.rs:225`). This is a real prototype compatibility failure,
  not an access failure or a successful source/package receipt. With no useful
  measured gain, the proof repair cost further supports **no-go**; no proof,
  pin, resource policy or budget was weakened to rescue it.
- C12 `aa1e5ba24ed27fe29c501b2e4455b3d6c530b67e`:
  [run 45590186006](https://github.com/microsoft/jpeg2000_rs/actions/runs/45590186006).
  **Success:** source and packaged production each verify 6,328 obligations,
  zero errors, with pinned Verus `0.2026.10.04.426d8b0`.
  Independently matched all 401 `src`/`specs`/`proofs` hashes in each receipt
  to the unchanged prototype. Existing `--no-lifetime` remains explicit;
  this does not verify lifetimes or establish measured source-function
  coverage. Passing this gate does not reverse the performance **no-go**.

Compact outcomes, receipt hashes and boundaries are committed in
[`verification-20261125.json`](data/verification-20261125.json); complete
downloaded receipts and failed-step diagnostics remain in the raw evidence.

The original snapshot's access blocker is historical, not the current gate.
No administrative bypass, protection change, merge, issue or publication was used.

Incremental coverage refresh read all 12 changed records in full:
91 issues /394 PRs, including new #492/#493. #485/#486/#488/#489 and their
qualification/integration #490/#491 are now merged; #472/#477/#479/#483 are
closed. Current merged main is `f4b2b7b29d38fa31bd74263913462bb67d6e5e4e`.
It is kept in a separate clean worktree, not substituted for the frozen `54abff4`
control. #492 continues the tracked private HT checkpoint work; #493 continues
tracked requested-sYCC geometry reuse. Its separate MCT investigation reports
that proposed plane-pointer/bounds work is already hoisted, not a missing patch.

Prepared an expanded 68-input corpus using pinned OpenJPEG 2.5.4:

| Family | Encoded cases | Actual coverage |
|---|---:|---|
| A | 8 | Two NASA photographs, 1.5MP RGB/gray, original 20.7MP RGB/gray, derived 12/16-bit gray |
| B | 24 | Same source variants, 9/7 at 10/40/100:1 |
| C | 14 | Actual 32/64 blocks and each individual coding-mode switch |
| D | 19 | Untiled/256/512/1024, five progressions, precincts, layers, RGB/gray thumbnails |
| F inputs | 3 | Actual 8192-square gray, tiled/untiled 5/3 and untiled 9/7 |

Both original photographs have independently inspected PD-USGov-NASA source
pages and pinned download hashes. The generator records attribution, original
and derived hashes, Pillow version, every encoder command, and parsed SIZ/COD
properties. High-precision low bits are explicitly synthetic and the 8K raster
is resampled; neither is misrepresented as native sensor capture.

All 68 expanded inputs complete full preflight on the frozen control and
OpenJPEG, with exact independent-source recovery on every reversible case,
including ERTERM/SEGMARK, actual 12/16-bit precision and all 8K streams.
The inventory retains every refusal, crash, mismatch and numeric observation;
acceptance is not normative numerical/conformance qualification. In particular,
new photographic 9/7 inputs expose pre-existing cross-decoder maxima of 2-6 on
some 8-bit cases and up to 10 on derived 16-bit gray. These are not an approved
new tolerance, an optimization regression, or a substitute for #299's original
four controls. Both decoders receive the same recorded 8GiB OS address-space cap,
separate from unchanged library resource limits.

The tooling now imports hash-bound external manifests, checks complete
little-endian 8/16-bit independent source oracles, and retains exact request
bindings. Eleven focused Python tests pass. No new decoder runtime, model,
proof, package default, release branch or acceptance tolerance changed.
A selected-case end-to-end smoke builds and records the actual clean
`f4b2b7b` decoder source separately; its shortened iterations are not speed
evidence. The full current-main A-D matrix has completed on all 65 relevant
cases in generic/consumer/native configurations, with the original 15-iteration
AND two-second, three-warmup, reversed-process protocol. The 8K streams are
reserved for separately bound discard/window requests, not mislabeled as
windowed-decoding measurements when decoded fully.

The report branch adds one manually selected `uncovered-evaluation` CI scope;
push/PR/default dispatch behavior is unchanged. It measures the 57 smaller A-D
cases on native x86-64 in generic/consumer/x86-64-v3/native profiles against
the same pinned `f4b2b7b` decoder. Large/8K hosted timing remains explicitly
excluded. Its artifact collector preserves canonical encoded inputs and raw
outcomes with hashes, omitting caches and pixel dumps. Cross-host pooling is
forbidden until input hashes match. The initial diagnostic dispatch
45591525447 was canceled rather than promote a run missing explicit CPU-model
and process-instruction evidence. Corrected
[run 45592665197](https://github.com/microsoft/jpeg2000_rs/actions/runs/45592665197)
then failed during public-photo acquisition with HTTP 403, before any
measurement. Its logs are preserved. The two unchanged, previously licensed
NASA originals (7.4MB total) are now vendored outside the decoder package with
separate credit, public-domain notice and mandatory hash checks. No alternate
identity, remote-access bypass or relaxed hash check is used.
[Run 45593985345](https://github.com/microsoft/jpeg2000_rs/actions/runs/45593985345)
completed successfully on an AMD EPYC 7763: 617,271 timing samples and 32
successful representative instruction outcomes. Its original 115,108,389-byte
artifact ZIP matches SHA256
`a17fdf65071b44e1489e522a660dc698c5efcf36d28bac91a3943f981625c303`;
all 4,341 retained members match their index hashes.
Independent analysis nevertheless found a **collector bug**: basename-based
cache pruning omitted the real `consumer` configuration's per-process/build
metadata while retaining its timing CSV. This incomplete four-profile artifact
is diagnostic, not promoted as a fully qualified matrix.

Cache pruning now recognizes actual Git/CMake/Cargo markers instead of
configuration names, explicitly checks retained process/instruction evidence,
and is regression-tested on `consumer` and a legitimate case named `cargo`.
A real collect/analyze round trip of the complete ARM64 matrix preserves all
1,170 process records and reproduces all 665,567 samples/medians/IQRs.
The x86 matrix must be rerun on one host rather than fabricate lost metadata
or splice profiles from different machines.
[Replacement run 45614658287](https://github.com/microsoft/jpeg2000_rs/actions/runs/45614658287)
is running at collector-fix commit `76e23b5`; its decoder remains pinned to
`f4b2b7b`. Decoder package contents remain
exactly 417 files; no tool, report or photograph is packaged.

All 57 cross-host source pixel hashes match, but three encoded 9/7 RGB
streams differ between encoders: day r10/r40 and night r10. Cross-target
output comparisons must use canonical matching stream bytes; those three
cases require an explicit same-stream ARM64 replay, not an assumption that
matching source pixels imply matching compressed inputs.
For the 54 byte-identical streams, both backends' output hashes match between
ARM64 and each of the retained generic/v3/native x86 profiles. This is a
strictly scoped result, not qualification of the missing consumer evidence
or the three different streams.
The three exact first-x86 streams have now completed a separate ARM64 replay
using the original unchanged timing binaries: **1,165 samples, 54 measured
processes, three profiles**. Combining only the 54 unchanged inputs with those
three replayed inputs yields **57 byte-identical streams**, with exact output
hash agreement for both backends across ARM64 and the three retained first-x86
profiles. Samples from the old different streams are never pooled. The final
replacement x86 artifact still must match these hashes and retain all four
profiles before its matrix is promoted.
The [replay latencies](data/canonical-replay-arm64-summary.csv),
[ratios](data/canonical-replay-arm64-ratios.csv),
[resources](data/canonical-replay-arm64-resources.csv),
[output hashes/numerics](data/canonical-replay-arm64-correctness.csv) and
[scope/source provenance](data/canonical-replay-arm64-provenance.json) are separate.

Window qualification now also compares each backend's actual selected output
with its own full-decode crop, before any timing. A real 32-square integration
case passes for both backends; 17 focused tooling tests pass. The queued 8K
requests completed after A-D, without competing owned measurement processes.
All three actual 8192-square streams qualify for discard 1/2/3 and the window;
all six real window/own-full-crop comparisons are exact.

### 8.1 Completed expanded current-main ARM64 matrix

Source remains `f4b2b7b`, not the original `54abff4` synthetic control.
Independent analysis reproduces all summary medians/IQRs from **665,567 raw
samples**, verifies all **1,170** fresh measured processes meet both
15 iterations and two seconds with three warmups, and checks worker/cap
metadata and all selected case/configuration combinations.

Geometric means of per-image Rust/OpenJPEG **typed-output median latency**:

| Configuration | A (8 cases) | B (24 cases) | C (14 cases) | D (19 cases) |
|---|---:|---:|---:|---:|
| Generic | 3.7159 | 5.5012 | 4.4011 | 3.6314 |
| Consumer | 3.7060 | 5.2260 | 4.2903 | 3.6065 |
| Native | 3.6770 | 5.2009 | 4.2654 | 3.5742 |

Lower than 1 would favor Rust; none of the 195 individual case/configuration
median ratios is below 1. Shared-host wall times remain **indicative**.
These new-source/new-corpus ratios cannot be subtracted from the old synthetic
ratios to attribute a merged PR speedup or a prototype effect.

All **123 reversible source-oracle checks** pass exactly. Both backends'
65 output hashes are invariant across all three profiles, and their generic
outputs also match the earlier frozen-control qualification on the same
65 inputs. Photographic irreversible maxima remain up to 6 for 8-bit RGB
and 10 for derived 16-bit gray, with per-image counts retained; these are not
newly approved tolerances or substitutes for the original #299 controls.

Largest observed timed-process RSS is 6,449,068 KiB for Rust and 1,198,940 KiB
for OpenJPEG typed output. These are **nonpaired peaks across different
cases**, including startup/input/warmups/destruction, not isolated stage
allocation counts. Full per-process resources remain available.

Distinct current-main tables, not replacements for the frozen tables:

- [Latency and IQR](data/expanded-current-arm64-summary.csv).
- [Per-image ratios and decoded MP/s](data/expanded-current-arm64-ratios.csv).
- [Per-process RSS/faults](data/expanded-current-arm64-resources.csv).
- [Per-image numerical maxima/counts and hashes](data/expanded-current-arm64-correctness.csv).
- [Class ratios](data/expanded-current-arm64-classes.csv) and
  [source/build/raw-hash provenance](data/expanded-current-arm64-provenance.json).

### 8.2 Actual x86-64-v3 arithmetic, not only allowed ISA flags

The preserved first x86 run's final consuming executable contains a real
256-bit integer loop in
[`rowwise::lift_rows`](https://github.com/microsoft/jpeg2000_rs/blob/f4b2b7b29d38fa31bd74263913462bb67d6e5e4e/src/transform/rowwise.rs#L280),
the bounded reversible 5/3 row-lifting path. At `0x7c030..0x7c09b`,
`vpaddq`/`vpsubq` operate on YMM registers; `vpsrad`, `vpsrlq` and `vpblendd`
implement signed 64-bit right shifts without AVX-512. This is arithmetic,
not merely vector copies, and does not imply that Q16 9/7 multiplication,
MQ, or every fallback vectorizes.

The same hash-checked v3 executable's separate gray-lossless Callgrind
profile records five calls on its update-stage `lift_rows` edge, with
3,051,592 inclusive instruction events. This confirms execution of the
function, not a stage-wall-time percentage or that every row takes its vector
branch. Existing range/alias guards and scalar/error paths remain present.

The [final-binary loop excerpt](data/x86-v3-lift-rows.asm),
[execution excerpt](data/x86-v3-lift-rows-callgrind.txt) and
[exact build/artifact/source provenance](data/x86-v3-codegen-provenance.json)
are retained independently of the incomplete first timing artifact.

### 8.3 Completed actual 8K partial requests

The three **8192 x 8192** grayscale streams are untiled 5/3, tiled-256 5/3,
and untiled 9/7. They are explicitly resampled NASA-derived sources, not native
8K sensor captures. Each real public-API request was independently qualified
and measured in generic/consumer/native configurations using the same
hash-checked `f4b2b7b` builds. Analysis verifies **7,781 samples and 216
full-protocol measured processes** across the four requests.

Generic profile, median milliseconds; ratio is Rust/OpenJPEG typed:

| Request | Stream | Rust ms | OpenJPEG ms | Ratio |
|---|---|---:|---:|---:|
| Discard 1 | Untiled 5/3 | 4499.18 | 1083.72 | 4.15 |
| Discard 1 | Tiled 5/3 | 3534.94 | 984.21 | 3.59 |
| Discard 1 | Untiled 9/7 | 2154.65 | 393.42 | 5.48 |
| Discard 2 | Untiled 5/3 | 2083.65 | 309.59 | 6.73 |
| Discard 2 | Tiled 5/3 | 1169.44 | 306.18 | 3.82 |
| Discard 2 | Untiled 9/7 | 1319.34 | 174.17 | 7.58 |
| Discard 3 | Untiled 5/3 | 1306.73 | 74.88 | 17.45 |
| Discard 3 | Tiled 5/3 | 468.13 | 89.67 | 5.22 |
| Discard 3 | Untiled 9/7 | 843.44 | 54.94 | 15.35 |
| Window 512-square | Untiled 5/3 | 10361.80 | 40.79 | 254.03 |
| Window 512-square | Tiled 5/3 | 41.82 | 10.71 | 3.90 |
| Window 512-square | Untiled 9/7 | 3642.99 | 15.77 | 230.98 |

Discard outputs contain 4096-square, 2048-square and 1024-square pixels;
the window is exactly `(2048,2048,512,512)`, with 262,144 output pixels.
Throughput uses those actual output sizes, not the full input area.
This measures the selected API itself, not a harness post-crop proxy.
Rust may still reconstruct an entire selected tile internally.

All 24 reversible case/request/profile comparisons match OpenJPEG exactly.
All six backend window outputs equal their own full-decode crops at the real
8K size, including independent full-source checks for the four reversible
backend outputs. The irreversible stream has maximum difference 1 for every
request, with per-image counts retained. Both backends remain bit-identical
across the three profiles for each selected request.

This confirms C11's **remaining intra-selected-tile** gap and that existing
tile selection already helps; it does not re-propose implemented tile culling
or discard entropy pruning. The 231-254 ratio is not a measured prototype
speedup or a safe gain bound. New filter-support/geometry, malformed-input,
work/deadline and selected-state proof prerequisites remain before adoption.
Shared-host times remain indicative.

Separate actual-window user-cycle profiles reinforce that this is not merely
a 5/3 arithmetic problem: untiled 5/3 Rust self samples are **85.62% Tier-1
(including MQ)** and **4.46% DWT**. Untiled 9/7 is **39.52% Tier-1** and
**35.80% DWT**. These are whole-process sampled self shares, not isolated stage
wall times or strict Amdahl ceilings; unknown/reconstruction self time remains
explicit. The profiler follows the actual window request and hash-checked
reused binary rather than accidentally profiling a full request.

Full [latencies/IQRs](data/partial-current-arm64-summary.csv),
[ratios/decoded throughput](data/partial-current-arm64-ratios.csv),
[process resources](data/partial-current-arm64-resources.csv),
[numerical statistics](data/partial-current-arm64-correctness.csv) and
[request/source/crop receipts](data/partial-current-arm64-provenance.json)
remain distinct from full-image A-D data.

The expanded one-command flow is
[`expanded.sh`](../../tools/bench-vs-openjpeg/expanded.sh). It prepares and
inventories the whole corpus, records actual source/binary identity, then runs
A-D and all three 8K streams at discard 1/2/3 and a 512-square window. Reused
builds retain their original recorded source identity; no current source label
is inferred from whatever checkout happens to host the script.

External class-G rights metadata was also inspected before acquisition:
`openjpeg-data` conformance's COPYRIGHT grants JPEG-2000 conformance-testing use
with the notice retained, but is not an unrestricted MIT data license.
Nonregression files have several distinct origins; its PngSuite subdirectory
has an explicit permissive grant, not a blanket grant over every bug attachment.
All 57 encoded conformance vectors have now been executed after local timing;
each pinned Git blob/size is checked and the mandatory notice retained.
The first diagnostic exposed raw-only input and unit-sampling dump assumptions
in the harness. Separate rebuilt drivers now use proper JP2 APIs and global-grid
canvas dimensions; raw full/reduced/window smoke checks still pass. Existing
timing binaries/data are not relabeled as these rebuilt drivers.

The corrected `f4b2b7b` inventory is **40 identical, 10 decoded with value
differences, and 7 Rust refusals; OpenJPEG decodes all 57**.
One refusal deliberately preserves the default 64-component resource limit on
a 257-component vector; six other marker/quantization/code-block refusals remain
unresolved compatibility findings. Value differences include maxima 158 on
`file2.jp2` and 598 on `p0_06.j2k`, not an invented accepted tolerance.
These unresolved baseline differences do not qualify full conformance or any
new optimization. The original #299 controls remain separate.
See the [complete outcome table](data/conformance-current-inventory.csv) and
[source/driver/rights provenance](data/conformance-current-provenance.json).
The separately licensed/mixed nonregression collection remains unexecuted.
External vectors and pixel dumps are not redistributed.

ARM Callgrind separately records 16 successful generic/consumer representative
A-D process counts. All eight native-profile attempts receive tool SIGILL on
unsupported instructions; those are explicit missing counts, not zeros or
library failures inferred from instrumentation. Actual uninstrumented native
decoding already passes the timing/correctness matrices. Native hardware
counters and actual-request stage profiles now complete successfully as a
separate fallback, without changing flags or weakening safety/resource limits.
The [instruction outcome table](data/expanded-current-arm64-instructions.csv)
retains successful counts and all refused native attempts.

The fresh collection covers representative A-D in generic/native and all three
actual windows in generic: **155 stage rows, 396 raw counter rows, and 22
three-repeat process-counter summaries**. Maximum observed instruction-count
relative range over the three repeats is **0.01149%**. Cycles, instructions,
IPC, branches, branch misses and L1 data misses are retained; LLC load misses
remain explicitly `<not supported>`, never zero.
See [sampled stages](data/expanded-current-arm64-stages.csv),
[raw counters](data/expanded-current-arm64-counters.csv),
[counter/IPC summaries](data/expanded-current-arm64-counter-summary.csv) and
[request/build/scope provenance](data/expanded-current-arm64-profiles-provenance.json).
