# Native compiler observations

This optional diagnostic producer uses Rustc's actual local definition table,
body ownership and optimized MIR. It observes nested and macro/derive-generated
functions, closures, runtime versus constant constructors, abstract declarations,
and non-function constant/static body owners. Call records retain compiler
identities and source locations. Compiler instance resolution distinguishes
concrete implementations, shims and virtual dispatch; generic/function-pointer
targets and destructor implementations remain explicitly unresolved.

Function, call and drop records also retain Rustc's `source_callsite` coordinates
alongside the original spans. Calls and drops identify whether their span came
from expansion. This distinguishes separate invocations of a macro whose
original call spans all point at the same library macro definition; it does not
replace those original spans or establish a native/Verus identity join.

It is **not** a qualified production denominator, a native/Verus erasure or
result-key crosswalk, complete runtime reachability, functional-contract
classification, lifetime proof, or a standards/conformance gate. Definition IDs
are capture-specific; do not join display spellings or equal counts as identities.
Compiler visibility is not effective public-reexport reachability.

The separate toolchain file pins the diagnostic SDK, including `rustc-dev`.
The build rejects a different compiler commit. It does not change the decoder's
Rust 1.88 support, production compiler, verifier pins, or verification mode.
Current executed qualification is Linux x86-64.

From the repository root:

```sh
TOOLCHAIN=nightly-2026-08-03
rustup toolchain install "$TOOLCHAIN" --profile minimal --component rustc-dev
cargo +"$TOOLCHAIN" build --locked \
  --manifest-path validation/native-inventory-driver/Cargo.toml \
  --target-dir target/native-inventory-driver
DRIVER="$PWD/target/native-inventory-driver/debug/jpeg2000-native-inventory"
RUSTC="$(rustup which --toolchain "$TOOLCHAIN" rustc)"
python3 validation/native-inventory-driver/test_driver.py --driver "$DRIVER" --rustc "$RUSTC"
```

For a production-library capture, choose a **new output file and target directory
for every run** so Cargo cannot substitute a cached compilation:

```sh
mkdir -p target/native-inventory/run1
JPEG2000_INVENTORY_CRATE=jpeg2000_decoder \
JPEG2000_INVENTORY_CAPTURE_ID=unique-run1 \
JPEG2000_INVENTORY_OUTPUT="$PWD/target/native-inventory/run1/default.json" \
RUSTC_WRAPPER="$DRIVER" \
CARGO_TARGET_DIR=target/native-inventory/run1/default-build \
cargo +"$TOOLCHAIN" check --lib --locked
```

Repeat with `--all-features`, another capture ID and fresh output/build paths.
Reject a missing report, failed command or mismatching capture/compiler identity.
Existing output files are never overwritten. Before using a capture, retain
source Git/dirty status before and after, source/tool/binary/SDK hashes, exact
commands and feature/target configuration. These provenance guards do not
independently authenticate a host or producer. Keep captures and failed runs
outside tracked source; do not relabel an old capture as a fresh run.

## Pinned Verus identity observations

The separate [Verus identity driver](../verus-identity-driver.rs) uses the
pinned compiler's public driver and actual erasure-hint function records.
Each record retains its structured canonical `Fun` identity, the compiler's
own diagnostic/result label, mode, span and optional actual result details.
Distinct internal impl paths are not guessed to match display names.
Imported functions and entries without result details remain visible; a
details entry is not itself a verified-function count or functional contract.
Result records also enumerate the complete canonical `func_details` map, not
only the initial erasure-hint definitions. Compiler display labels need not be
injective: every result retains its canonical identity and the number of
canonical results sharing that label. Shared labels are explicitly marked;
never deduplicate them into a claimed per-source-function proof count.

This is still **not** a qualified native production denominator, native/Verus
erasure correspondence, effective reachability or functional classification.
Coverage fields remain `not-measured`. The ordinary decoder/proof commands and
their trust boundary are unchanged. This optional SDK client is not a
replacement release/proof attestor.

The client requires the complete libraries from the exact Verus
`426d8b01e7ffb910a36c15e1f870ff985bb61eef` build and its Rust 1.98.1 SDK.
Some binary-only distributions do not contain these development libraries.
Choose the matching `serde_json` rlib from that same build explicitly; do not
substitute libraries from another compiler build when multiple files exist.

```sh
export VERUS_ROOT=/path/to/pinned/full-verus-build
export VERUS_SERDE_JSON_RLIB=/path/to/pinned/full-verus-build/deps/libserde_json-HASH.rlib
SDK="$(rustc +1.98.1 --print sysroot)"
mkdir -p target/verus-identities
RUSTC_BOOTSTRAP=1 rustc +1.98.1 validation/verus-identity-driver.rs \
  --edition=2021 -L "dependency=$VERUS_ROOT/deps" \
  --extern "rust_verify=$VERUS_ROOT/librust_verify.rlib" \
  --extern "vir=$VERUS_ROOT/libvir.rlib" \
  --extern "serde_json=$VERUS_SERDE_JSON_RLIB" \
  -o target/verus-identities/driver
mkdir -p target/verus-identities/sdk
cp "$VERUS_ROOT/cargo-verus" target/verus-identities/sdk/cargo-verus
cp target/verus-identities/driver target/verus-identities/sdk/verus
python3 validation/test_verus_identity_driver.py \
  --driver "$PWD/target/verus-identities/driver" \
  --verus-root "$VERUS_ROOT" --sdk-lib "$SDK/lib" \
  --cargo-sdk "$PWD/target/verus-identities/sdk" -v
```

The bootstrap setting above enables the optional Rustc-private SDK client,
as used by the pinned compiler itself; it does not change decoder compilation,
verification options or solver budgets. The real controls compare exact
result details with the unchanged pinned executable and reject failed proofs,
overwritten captures and mismatching compiler pins.

For a new direct compiler capture, supply the exact Rustc/feature/import
arguments and retain source/SDK/library/binary hashes and before/after source
status, just as for the native producer:

```sh
LD_LIBRARY_PATH="$SDK/lib" \
JPEG2000_NAMES_OUTPUT="$PWD/target/verus-identities/new-run.json" \
RUSTUP_TOOLCHAIN=1.98.1-x86_64-unknown-linux-gnu \
target/verus-identities/driver input.rs --crate-name control --no-lifetime
```

For Cargo captures, the unchanged pinned `cargo-verus` executable selects its
sibling `verus` SDK client. Retain and compare the copied Cargo executable's
hash; installed tools are not replaced. The client uses the same public
Cargo argument/dependency routing, delegates ordinary dependencies and compiler
version/trait-check subprocesses to the original pinned tools, and captures
only the explicitly selected crate:

```sh
PATH="$PWD/target/verus-identities/sdk:$PATH" \
LD_LIBRARY_PATH="$SDK/lib" JPEG2000_NAMES_CRATE=jpeg2000_decoder \
JPEG2000_NAMES_OUTPUT="$PWD/target/verus-identities/cargo-new-run.json" \
RUSTUP_TOOLCHAIN=1.98.1-x86_64-unknown-linux-gnu \
cargo verus verify --features verus --locked --fwd-verus-args-to roots \
  --target-dir target/verus-identities/cargo-new-build --lib -- \
  --no-lifetime --output-json
```

Direct and Cargo invocations are different profiles: dependencies, imports and
compiler cfg must not be inferred to match. The real Cargo control separately
compares exact result details with the original pinned Cargo workflow.
Qualification of a production denominator, native/Verus erasure equivalence,
all feature branches and full functional contracts remains separate.
