# Uncovered performance candidates evaluation

Execution: 24-25 November 2026. Branch: `perf/eval-report`.
Decoder baseline: `54abff44a778b6c210d580770286a531370550b6` (`origin/main` at start).

**Status: measured partial evaluation, not the full definition of done.**
Coverage is verified, an available ARM64 matrix is reproducible, and two
isolated experiments were tested and measured. Other uncovered mechanisms have
explicit needs-more-data cards. Exact-source Verus, native x86-64/v3,
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

**Verus: not run, not a theorem failure.** `cargo verus` is unavailable locally;
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
  pass. Verus blocked; cross-target execution untested.
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
  acceptable. Exact-source verifier access is blocked.
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
  Verus blocked; cross-target execution untested.
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

1. Restore exact-source proof execution and complete H/C9 corpus/ISA gaps.
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
- [ ] Exact-source Verus on both prototypes: local tool absent / remote push 403.
- [ ] Complete A-G corpus, isolated stage-wall timers and residual attribution.
- [ ] Native x86-64/v3/AVX2, cross-target determinism and missing precision cases.
- [ ] Remaining uncovered prototypes after proof/numerical/error prerequisites.

**The complete prompt's definition of done is not met.** This report uses its
explicit blocked-candidate reporting fallback, without fabricated measurements,
weakened proof/safety guarantees, or claims that missing cells passed.
