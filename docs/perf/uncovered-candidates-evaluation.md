# Uncovered performance candidates: blocked evaluation

Date: 2026-11-24

**Status: incomplete; Step 0 coverage gate blocked.** This is a persistent
blocker report, not a completed performance evaluation. No timing, speedup,
correctness, proof, or coverage claim is made.

## Executive summary

The requested evaluation could not pass its mandatory first step. Both a direct
read of issue #440 and an issue-list request through the GitHub connection
failed with organization SAML enforcement. The issue/PR contents needed to
distinguish remaining work from existing work were unavailable.

The separate Git transport did successfully fetch the configured origin refs.
This does not establish access to issue/PR contents or complete branch coverage.
No candidate was assumed to be uncovered from its name or from the supplied
prompt's provisional matrix.

The current shell also did not expose the necessary Rust/C toolchain or
profilers, and the alternative DevBox connection failed during initialization.
No dependencies were installed and no shared-machine settings were changed.

Consequently:

- The crate's current performance relative to OpenJPEG 2.5.4 is unknown.
- No baseline, stage shares, candidate measurements, or combined stack exist.
- Every candidate needs more data; none qualifies as a measured go or no-go.
- No prototype branches, issues, or pull requests were created.
- Only this report was created, on `perf/eval-report`.

## Evaluation provenance

| Item | Observed value |
|---|---|
| Repository | `microsoft/jpeg2000_rs` |
| Default-branch reference | `refs/remotes/origin/main` |
| Report base, after successful fetch | `54abff44a778b6c210d580770286a531370550b6` |
| Original active branch | `openjpeg-compat` |
| Original active commit | `712cab95366940bf16c2344d350b909a8009059c` |
| Shell kernel/architecture query | `uname -sm`: `Linux aarch64` |
| Machine sharing | Shared environment; no CPU/governor/turbo changes attempted |
| Toolchains, compiler flags, OpenJPEG build | Not established |
| Corpus provenance and encoding commands | Not established |

The original checkout was clean at initial inspection. A separate worktree was
created from the refreshed default-branch reference so the report would not
switch or modify the original active checkout.

## Step 0: coverage evidence and gate

### GitHub requests actually attempted

1. `issue_read`, owner `microsoft`, repo `jpeg2000_rs`, issue number `440`,
   method `get`:

   > 403 Resource protected by organization SAML enforcement. You must grant your OAuth token access to this organization.

2. `list_issues`, same repository, newest first, requesting number, title and
   state:

   > Resource protected by organization SAML enforcement. You must grant your OAuth token access to this organization.

These are authorization-error quotations, **not quotations from issues**.
The issue/PR exports were not obtained. After the same authorization failure
on both requests, additional issue/PR reads through that connection were not
attempted. No alternate identity or access-control workaround was used.

Issues #440 and #446 through #456 remain unread, as do the background issues
#132, #289 and #299. The wider keyword-based issue/PR review has not happened.
In particular, no assertion about #299's current numerical baseline or #289's
deadline semantics is justified.

### Git commands actually run

```sh
git status --short
git branch --show-current
git remote -v
git symbolic-ref --quiet refs/remotes/origin/HEAD
git fetch origin --prune
git rev-parse origin/main
git branch -r --list '*perf*'
```

The fetch succeeded. The local remote-tracking performance-branch query
returned no matches. This is not a full remote branch export and does not
prove that any candidate is untracked. Branch and merge titles are insufficient
evidence of issue/PR scope.

### Coverage matrix

An unverified status is intentional: it must not be substituted with
"not covered", "partly covered", or "covered" without reading the actual
issue/PR evidence. The supplied prompt's provisional references are search
leads only.

| ID | Candidate | Covering issues/PRs | Verdict | Exact remaining scope | Issue/PR quotation |
|---|---|---|---|---|---|
| H | OpenJPEG head-to-head harness | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C1-HT | Narrow HTJ2K coefficients | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C2 | Stripe flags, context tables, block specialization | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C3 | MQ hot loop | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C4-97 | Irreversible inverse DWT | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C5 | Whole-plane kernels and stage fusion | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C6 | Multithreading | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C7 | Work/deadline accounting | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C8 | Scratch/buffer reuse beyond replay | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C9-ISA | Build/benchmark ISA parity | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C10 | HTJ2K readers and decoding tables | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C11 | Region/discard-level pruning | Unverified | Unverified | Unverified | Unavailable: SAML gate |
| C12 | Proof erasure and inlining | Unverified | Unverified | Unverified | Unavailable: SAML gate |

No extra X-series candidate was inferred without the required review.

## Step 1: harness, corpus and baseline

### Tool availability evidence

```sh
command -v gh rustc cargo cmake cc perf valgrind taskset
rustc --version
cc --version | head -n 1
```

Only `/usr/bin/taskset` was returned by the tool lookup. The version probes
reported `rustc: command not found` and `cc: command not found`.
These observations describe this shell's PATH, not every installation that
may exist elsewhere on the host.

An attempt to connect the DevBox MCP server failed before its initialization
handshake completed, with exit code 1 and `ERR_DLOPEN_FAILED` in the
`keytar` module stack. The exact missing native library was not established.

No benchmark command was run. There is therefore no generated CSV, corpus
classification, memory profile, instruction count, or assembly evidence.
An empty or synthetic CSV would not satisfy the requested raw-results
deliverable and has deliberately not been provided.

| Required measurement | Status |
|---|---|
| In-memory, equivalent-output Rust/OpenJPEG baseline | Not run |
| Native-output baseline | Not run |
| Class A-G corpus and correctness inventory | Not established |
| Baseline/default, consumer, x86-64-v3, native build matrix | Not run |
| Stage shares and hardware counters | Not measured |
| Allocation counts and peak RSS | Not measured |
| Reduced/windowed and multi-thread comparisons | Not run |
| Before/after #299 per-image differences | Not measured |
| Cross-target/thread-count determinism | Not tested |

The observed aarch64 shell is not evidence that an x86-64-v3 runner exists.
ISA comparisons and any multi-machine work must record their own machines,
flags and matched reference builds.

## Step 2: candidate cards

The following status applies to **each** card:

- Coverage: unverified; blocked by Step 0.
- Hypothesis confirmation and source-line evidence: deferred, not assumed.
- Baseline stage share: not measured for any corpus class.
- Prototype branch and lines changed: none.
- Correctness, bit-exactness, #299 before/after statistics, and determinism:
  not tested; no runtime changes made.
- Verus: not run; no source or proof changes made.
- Implementation effort and risk: not estimated without current scope/code.
- Recommendation: **needs more data**.
- Before/after time, change, and Rust/OpenJPEG ratios: unavailable in every
  configuration; no per-class result table can be populated honestly.

### H: head-to-head benchmark harness

First verify whether existing harness work already covers this request, then
reuse it where appropriate. A new uncompiled driver would not establish a
baseline. Requires authorized coverage evidence and a working build environment.

### C9-ISA: ISA parity

Requires H, the actual #449 settings, matched C/Rust flags, and appropriate
runners. No AVX2, vectorization, or CI-configuration recommendation is supported
by the current evidence.

### C3: MQ decoder hot loop

Requires verified remaining MQ scope, stage profiling, and inspection of current
invariants and proofs. No checked operation was removed speculatively.

### C2: stripe flags and table-driven contexts

Requires current narrow-word/compact-storage work and its interaction boundaries
to be read first. No duplicate storage or context implementation was introduced.

### C4-97: 9/7 inverse DWT

Requires #299's actual baseline, per-image difference counts and maxima, and
the current wavelet/layout implementation. None of the proposed floating-point,
narrow-integer, or layout-only options has been evaluated.

### C5: whole-plane kernels and fusion

Requires current arithmetic/output semantics, stage shares, and range/error
invariants. No claim is made that any proposed fusion is currently absent.

### C7: coarser accounting

Requires #289, the existing work-limit model, and a derived/tested deadline
overshoot bound. No accounting or deadline check was weakened.

### C8: scratch and buffer reuse

Requires coverage beyond already-tracked replay reuse and allocation/zeroing
profiles. No allocation-saving or memory-use claim is supported yet.

### C12: proof erasure and inlining

Requires current proof wiring, compiled assembly and profiling with both
relevant profiles. Proof-related runtime checks were not assumed redundant.

### C1-HT: narrow HTJ2K coefficient path

Requires current HT storage coverage and representative HT streams. No
coefficient-width or wide-fallback hypothesis has been confirmed.

### C10: HTJ2K bit readers and tables

Requires current reader/table code, HT stage profiles and conformance checks.
No throughput or reader-width change was attempted.

### C11: region/discard pruning

Requires checking current public API support and decode orchestration after
the coverage gate. Support or lack of support was not inferred from the prompt.

### C6: multithreading

Requires current threading coverage/API, #289 semantics, and a baseline.
No opt-in knob, workers, scheduling threshold, or scaling claim was introduced.

## Step 3: stack, ranking and issue drafts

There are no measured go candidates, so there is no `perf/eval-stack`, ranking,
combined Rust/OpenJPEG ratio, or draft issue. No issue or PR was filed. This
does not imply that any candidate failed the performance thresholds.

The implementation order is not yet evidence-backed. The next valid order of
work is coverage verification, harness/baseline/profiling, then candidate
selection and isolated prototypes.

## Unblocking and reproduction

1. Authorize the GitHub connection's OAuth token for the `microsoft`
   organization's SAML SSO, or supply authorized issue/PR/branch exports.
2. Read #440, #446 through #456, #132, #289 and #299 in full, and complete the
   prompt's wider title/body keyword review. Replace the unverified matrix
   with quoted, current evidence before evaluating remaining scope.
3. Restore a working development connection or expose the required Rust/C
   build and profiling tools. Recheck availability in that environment.
4. Inspect existing benchmark/validation code and reuse it. Establish the
   licensed corpus, equivalent-output OpenJPEG 2.5.4 reference with
   `-ffp-contract=off` for correctness, rerunnable harness, and raw baseline.
5. On this shared host, treat wall-clock timings as indicative; collect
   instruction counts where permitted. Do not change global CPU settings.
6. Only then create isolated prototype branches, run the required correctness
   and proof gates, measure the candidates and any go stack, and draft issues.

No all-matrix rerun command can truthfully be supplied until the harness and
corpus have been established. The commands above reproduce the availability
checks; the named GitHub operations reproduce the authorization checks.

## Completion checklist

- [ ] Coverage matrix verified against current issues and PRs
- [ ] Harness, licensed corpus, baseline and stage shares established
- [ ] Every uncovered candidate measured or individually investigated
- [ ] Required correctness, numeric, determinism and proof checks run
- [ ] Every go candidate and combined stack measured against OpenJPEG 2.5.4
- [ ] Draft issue text prepared for each measured go
- [x] Persistent report records the blocked gate without fabricated results
