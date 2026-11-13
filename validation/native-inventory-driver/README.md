# Native compiler observations

This optional diagnostic producer uses Rustc's actual local definition table,
body ownership and optimized MIR. It observes nested and macro/derive-generated
functions, closures, runtime versus constant constructors, abstract declarations,
and non-function constant/static body owners. Call records retain compiler
identities and source locations. Compiler instance resolution distinguishes
concrete implementations, shims and virtual dispatch; generic/function-pointer
targets and destructor implementations remain explicitly unresolved.

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
