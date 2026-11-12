# Contributing

Please use [SECURITY.md](SECURITY.md), not public issues, for suspected
vulnerabilities or sensitive input files.

## Development setup

Install rustup; the checked-in toolchain selects the tested Rust version.
The default decoder build has no external Cargo dependencies. The optional
`verus` feature enables the pinned verification dependency. Validation tooling
has its own pinned Python requirements.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r validation/requirements.txt
cargo test --all-targets --locked
cargo test --doc --locked
```

## Required local checks

### Minimum supported Rust version

Ordinary decoder builds support Rust 1.88.0. Keep runtime changes compatible
with this minimum; CI runs the following checks independently of the newer
development toolchain pin:

```sh
rustup toolchain install 1.88.0 --profile minimal
cargo +1.88.0 test --no-default-features --all-targets --locked
cargo +1.88.0 test --no-default-features --doc --locked
cargo +1.88.0 check --no-default-features --release --all-targets --locked
```

The optional `verus` feature and verification tools use their separately pinned
toolchain, not the runtime minimum. Do not lower their pins to run these checks.

### Full development checks

External numerical checks require OpenJPEG's `opj_compress` and
`opj_decompress` (Debian/Ubuntu package `libopenjp2-tools`). Use
`all --no-external` only when intentionally omitting native comparisons;
that does not establish numerical agreement.
HTJ2K comparisons additionally use the pinned scalar OpenJPH build described
in [validation instructions](validation/VALIDATION.md#independent-htj2k-checks).
Build those tools and configure `OPENJPH_ENCODER` and `OPENJPH_DECODER` before
running the separate HT gate.

```sh
cargo fmt --all -- --check
cargo test --all-targets --locked
cargo check --release --all-targets --locked
cargo clippy --all-targets --all-features --locked -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --locked
python -m unittest discover -s validation/tests -v
python validation/run-validation.py all
python validation/run-validation.py htj2k
python validation/run-validation.py resources
cargo check --manifest-path fuzz/Cargo.toml --all-targets --locked
cargo test --manifest-path fuzz/Cargo.toml --lib --locked
diff -u validation/expected-package-files.txt <(cargo package --list --locked)
cargo package --locked
```

The package-list comparison uses a Bash-compatible shell. Follow [PROOFS.md](PROOFS.md)
for the root `cargo verus verify --features verus` command, required pinned
toolchain/arguments and fail-closed report collection, and
[validation instructions](validation/VALIDATION.md)
for optional external oracles and official-vector runs.
The representative resource gate additionally requires Linux and GNU Time.
`cargo package` builds and verifies the packaged source locally; it does not
publish the crate or change `publish = false`.

## Implementation and review

- Keep one executable implementation under `src/`.
- Preserve typed failure and resource-limit behavior.
- Add a focused regression before changing decoder semantics.
- Keep specification helpers connected to concrete implementation behavior.
- Keep normative/selected-policy models on the [auditor reading path](specs/README.md);
  put invariant-only witnesses in proof support, and prove presentation
  equivalences instead of making auditors infer numeric normalization.
- Pin public reference revisions and preserve required third-party notices.
- Do not commit standards text, purchased vectors, personal credentials, native
  oracle binaries, local research material, or generated run reports.
- Minimize a redistributable failing input before adding it as a regression.
- Avoid unreviewed additions to the supported standards profile.
- Preserve `unsafe_code = "forbid"` in both Cargo manifests and the library's
  crate-level prohibition. Safe code still needs panic, arithmetic, resource
  and functional review; do not substitute a token scan for those checks.
- Keep maintained JSON inputs in [validation/](validation/) and generated
  evidence in ignored `target/`. Use issues/PRs for execution tracking rather
  than committing session plans, run reports or approval records.

## Coordinated proof work

The repository's [Verus proof worker](.github/agents/verus-proof-worker.agent.md)
is for a coordinator-assigned, bounded implementation task. Its profile requests
GPT-6.1 Sol, but selecting the profile alone does not guarantee the task's
top-level model: `gh agent-task create --custom-agent` can still use Auto.
Set both `model: gpt-6.1-sol` and `custom_agent: verus-proof-worker` explicitly
when dispatching through the [agent-tasks REST API](https://docs.github.com/en/rest/agent-tasks/agent-tasks#start-a-task).
Verify the resulting session's model in platform metadata or original runner
logs, not the worker's self-identification. Stop on a mismatch or unavailable
model; do not silently fall back. A task must name its
accepted source base, prerequisites, actual producer/consumer boundary and
required gates. Dependent tasks wait until their prerequisite changes are
accepted on `main`; they must not repeat work from an older base or create
unreviewed parallel edits to the same proof chain.

The coordinator audits exact PR-head evidence, keeps remaining proof work
explicit, and does not infer completion from task status or a focused verifier
run. Cloud agent profiles and setup workflows become usable after merging
them into the default branch. They do not authorize merges, pin/budget
changes, repository visibility changes or crate publication.

## Fuzzing

The [fuzz crate](fuzz/) provides arbitrary-input and structured-input targets.
Compile targets independently from the main crate:

```sh
cargo check --manifest-path fuzz/Cargo.toml --all-targets --locked
cargo test --manifest-path fuzz/Cargo.toml --lib --locked
cargo run --manifest-path fuzz/Cargo.toml --bin arbitrary_codestream -- \
  -runs=1000 -max_len=4096
```

The fuzz library tests also exercise the structured positive-input builders,
including empty input and every selector. Nested association fixtures retain
at least two immediate children per association.

Smoke runs do not establish coverage or sanitizer completeness. Use an
appropriately instrumented cargo-fuzz/nightly setup for sustained campaigns.
Keep campaign output outside tracked source, and include execution budgets and
reproduction commands when reporting a result.

With cargo-fuzz and a nightly toolchain installed, run a bounded,
AddressSanitizer/coverage-guided check on a copy of the structured seeds:

```sh
mkdir -p target/validation/fuzz-corpus
cp -R fuzz/corpus/structured_framing/. target/validation/fuzz-corpus/
cargo +nightly fuzz run structured_framing target/validation/fuzz-corpus -- \
  -runs=1000 -max_len=4096 -timeout=20 -rss_limit_mb=2048 \
  -artifact_prefix=target/validation/
```

This is still a smoke budget, not a sustained coverage campaign. Do not mutate
the checked-in corpus during exploratory runs.

Fuzz targets share a tighter profile than the production defaults: one-MiB
input/metadata, four-MiB decoded storage, 256 code-blocks, 4,096 packets,
256 JPIP fragments and one million work units. These bounds leave room for
AddressSanitizer overhead within the process RSS cap. Larger production
resource profiles need separate representative-image budget tests.

For a longer bounded run, replace `-runs=1000` with
`-max_total_time=60 -print_final_stats=1`. Apply the same explicit time, input,
timeout and RSS budgets to all seven targets. Capture the source commit/dirty
state, harness and binary hashes, nightly/cargo-fuzz versions, final execution
counts, coverage counters, and peak RSS. Keep corpus growth and crash artifacts
in the ignored output directory; a successful minute is not exhaustive coverage.
