# Reversible ROI support experiment

This unpublished counting-only tool uses existing public parsing, planning and
packet APIs. It still entropy-decodes **every** block in each selected tile;
there is no pruning, changed work charge, relaxed limit or new decoder knob.
CSV records exact block/coefficient counts and observed decoded segment bytes
and passes inside/outside a separable reversible 5/3 dependency mask. Bytes and
passes are not MQ decisions, wall-time gain, or a normative proof of pruning.

The mask reverses predict/update dependencies, including symmetric boundary
extension and odd origins, then propagates required LL support through levels.
Tests compare masked/unmasked public inverse-5/3 output for all small intervals.
The first executable scope is one unit-sampled component, standard isotropic
5/3 and contiguous tile parts. Unsupported scope fails explicitly.

```sh
cargo test --manifest-path tools/roi-support-study/Cargo.toml
cargo run --release --manifest-path tools/roi-support-study/Cargo.toml -- \
  INPUT.j2k 2048,2048,512,512 > counts.csv 2> summary.txt
```

Default library code, API, model and proof files are unchanged. Eligibility is
not permission to skip: error/resource/deadline equivalence and selected-state
refinement remain prerequisites for a subsequent production-path experiment.
