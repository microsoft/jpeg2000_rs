# Explicitly sized final-part EOC recovery (#440)

## Classification and policy

T.800 (06/2019), A.4.4 requires one terminal EOC per codestream. Its second
note acknowledges useful decoding of corrupted data without that marker.
The missing-EOC original is therefore nonconforming: strict APIs retain their
`Truncated` rejection, not a new strict acceptance. The acquired reference
SHA256 is `9932e967462cd56a193db87117917e74734fb385913bf51d1f52fb0428924e1c`.
Selected2024 full text was not acquired or claimed reconciled.

The explicit existing raw/PDF-compatible recovery now admits a positively
sized sole part only when:

- SIZ advertises one tile and the normal checked headers contain COD/QCD/SOD;
- Isot and TPsot are zero and TNsot is one;
- Psot is positive and its actual SOT start plus length equals EOF;
- the bounded marker-aware body traversal encounters no existing EOC,
  additional SOT or unrelated marker;
- existing input/copy-work/resource admission permits appending exactlyFFD9.

No part, payload or pixel is inferred. Matching length is structural admission,
not proof of complete packets. Normal layout inspection and strict decoding
still validate the repaired input; a structurally admitted empty packet body
does not produce a successful decoded image. Existing Psot0/count0-or1
recovery is unchanged. Positively sized unknown-count parts remain outside
this deliberately bounded policy.

## Original and independent control

The MIT-licensed fixture is from
[Hayro e7ada1354dff4041cdeed3d8ba56fe01b6186132](https://github.com/LaurenzV/hayro/tree/e7ada1354dff4041cdeed3d8ba56fe01b6186132),
path `hayro-jpeg2000/tests/streams/tile_parts_missing_eoc.j2k`.
SHA256: `31ca91d8ad893468b21e5452f93fd46973a3e370829e255d33ed8d4e8f1b7c44`.
The copied file is unchanged; adjacent LICENSE-MIT retains upstream attribution.

The original has7587 bytes, SOT at119 and Psot7468, placing the declared
part end exactly at EOF. Baseline current-main strict decoding rejects it at
byte7587 with `Truncated`. The independent complete control changes only the
missing EOC by appendingFFD9. Ordinary strict decoding of that control and
compatible decoding of the original return identical128x96 unsigned8-bit
grayscale samples.

All12288 control samples also match native OpenJPEG2.5.4 exactly. Sample-byte
SHA256: `b99f348fe8bd86f3bb26bad6217f37abfa5e182244dff74459b1bec27c1d8106`.
Reference acceptance is a numerical cross-check, not the normative basis.

The original's observable successful report is:

| Field | Value |
|---|---:|
| appended_eoc | true |
| original_codestream_bytes | 7587 |
| effective_codestream_bytes | 7589 |
| preflight_work_units | 7461 |
| repair_copy_bytes | 7589 |

These are the existing separate-stage counters, not global decoding work or
peak physical memory claims. Joint preflight/copy admission is15050 work
units; ordinary decoding retains its separate limits. The intact control
reports no repair and zero copy bytes.

## Proof correction and tests

The prior exact framing model deliberately excluded all positive Psot.
The actual SOT reader result is now checked against its post-read input extent
and the same predicate is composed into the source framing model. Original
strict parsing, marker ordering, entropy arithmetic, append-only copy model,
one fallible reservation and report/resource contracts are unchanged.
No new assumption, budget increase, verifier-only implementation or exclusion
is introduced.

Focused tests cover both explicit and open-ended raw/reconstructed recovery,
raw/JP2 PDF paths, exact pixels/origins/reports, copy refusal, joint-work/input
thresholds, output limits, wrong lengths/tile/part/count, truncation and
unexpected EOC trailers. The original fixture suite separately checks actual
inspection/decode agreement for the successful input and continued strict
rejection; adjusted-length empty payload demonstrates that matching a boundary
alone is not a decoded success.

```sh
cargo test --lib recovery::tests
python -m unittest validation.tests.test_sized_eoc_recovery -v
```

The validation example accepts `decode pdf`, `inspect pdf` and `recovery pdf`
for the explicit image-stream policy, not for parsing an entire PDF document.
The report command exposes the actual decoder report without replacing image
tests; native in-package tests cover allocation refusal and input/copy limits.
