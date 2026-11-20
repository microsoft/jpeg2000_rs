# Strict mixed-component spatial progression (#425)

## Classification and normative basis

This corrects a **Part 1 decoding defect**, not damaged-input recovery or a
Hayro-specific extension. T.800 (06/2019), A.6.1/A.6.2 permit the COD/COC
component styles in these streams. B.12.1.3–B.12.1.5 and equation B-20 define
RPCL/PCRL/CPRL using reference-grid positions, individual `NL(i)`, and the
special first-position test at nonzero tile origins. Equal reference-grid
precinct spacing does not imply equal first positions after ceiling division.

The inspected reference is the acquired 2019 text, PDF SHA-256
`9932e967462cd56a193db87117917e74734fb385913bf51d1f52fb0428924e1c`.
The payment-controlled 2024 full text was **not** inspected. OpenJPEG
acceptance is corroboration, not a conformance proof.

## Implementation and proof boundary

Previously `Part1PacketGrid` contained counts only, and the proved candidate
model specified interleaving *local precinct ordinals*. Thus those proofs did
not establish the normative spatial ordering.

Input-derived grids now additionally own per-component/resolution spatial
descriptors. Existing component geometry/downsampling/precinct helpers supply
their counts and coordinates. A bounded reference-grid raster maps spatial
candidates back to real precinct ordinals; absent positions are skipped, not
decoded as empty packets. The grid step uses the GCD of mapped spacings (the
minimum for Part 1 power-of-two spatial grids), following the efficient-scan
permission in B.12.1.3's note. Anisotropic precincts are supported; the scan's
actual Cartesian size, including POC windows, is checked against the existing
work limit with checked arithmetic before packet traversal.

Count-only `PacketGrid` constructors and their APIs remain unchanged.
LRCP/RLCP retain ordinal traversal and their original work admission. POC
component/resolution offsets are applied before spatial lookup; existing
prior-window visitation suppression, selections and final packet counts remain.
One fallible metadata-owner reservation is added to geometry-derived grids.
Recovery reservation-frontier controls account for that owner.

The actual implementations, not substitutes, have focused Verus coverage:

- `packet::spatial` and `packet::progression`: mapping, checked scan arithmetic,
  limits, candidates, default traversal and POC state transitions;
- `decode::spatial`: source selectors, geometry, first-position derivation,
  bounded owner construction, refusal/error results and complete fold;
- `decode::geometry`, `derive_packet_grid*`: original count producers and
  their actual spatial-owner composition;
- `decode::planning`, `plan_progression_tile_at_selected`: actual tile-plan
  composition;
- `specs::spatial_geometry`, `specs::spatial_grid_composition` and the dependent
  packet/grid/plan models: complete allocation traces and caller joins.

The old count-only models remain as explicit producer stages, not contracts
for the final geometry-derived grid. No assumptions, trust, proof-budget
increases, verification exclusions, experimental word/vector changes or
recovery relaxations are introduced. Whole-source/archive gates remain the
parent integration step.

## Original fixtures and exact numerical regression

`fixtures/hayro-mixed-progression/` contains the unmodified
`packets_mixed_levels_{cprl,pcrl,rpcl}.j2k` inputs from
[LaurenzV/hayro at e7ada1354dff4041cdeed3d8ba56fe01b6186132](https://github.com/LaurenzV/hayro/tree/e7ada1354dff4041cdeed3d8ba56fe01b6186132).
Copyright (c) The Hayro Authors; the accompanying `LICENSE-MIT` applies.

All three use bounds `(37,21)–(165,117)`, tiles `48×40` originating at
`(10,5)`, three components, four layers, reversible DWT and no MCT.
Component decomposition levels are respectively 4, 2 and 3. Their precinct
exponents map to 32-unit reference spacings, with different rounded first
positions.

The checked-in `reference_{0,1,2}.pgx` planes are the supplied native OpenJPEG
2.5.4 output. All three original inputs reconstruct the same three planes.
Strict decoding on the fix, without any other compatibility fix, gives:

| Progression | Compared samples | Exact samples | Maximum absolute error |
|---|---:|---:|---:|
| CPRL | 36,864 | 36,864 | 0 |
| PCRL | 36,864 | 36,864 | 0 |
| RPCL | 36,864 | 36,864 | 0 |

Baseline `d5071f5` and published 0.2.1 rejected these streams
(CPRL/PCRL `InvalidCodeBlock`, RPCL `InvalidPacketHeader`).

Run the reproducible per-sample, strict-error and budget regressions with:

```sh
python -m unittest validation.tests.test_mixed_progression -v
cargo test --lib spatial_
```

The Python suite uses `framework.build_subject()` and bounded processes for
expected errors. Rust tests use only native in-package data; no Rust test
includes an excluded validation fixture. Literal native cases additionally
exercise unequal spacings, two-dimensional ordering, overlapping and offset
POCs, invalid spatial metadata, allocation refusal/restoration, and a real
cross-axis raster whose spatial work exceeds its count-only work.

Original stream SHA-256:

- CPRL: `41ed927e2a784ccccdc16987d850ef453c50ba72cfa8d2293362cf841a2b9609`
- PCRL: `a52bd009ea2a54129c372765a4e2aaf8cfd0c0652595e7da14aea4b78e9b157c`
- RPCL: `9d5c0737ec5744c3882066bac15d45227c8e1e7cdc11317ff797de8872681d44`
