# Reserved parameterless marker compatibility (#426)

## Classification

This is a strict decoder correction, not a recovery. ITU-T T.800 (06/2019),
Annex A.1.2, Table A.1 and A.1.3 distinguish FF30-FF3F from length-bearing
marker segments and require the decoder to skip these parameterless markers.
The acquired publication is ISO/IEC 15444-1:2019 / T.800 (06/2019), SHA256
`9932e967462cd56a193db87117917e74734fb385913bf51d1f52fb0428924e1c`.
The separately selected 2024 full text was not acquired or silently inferred.

The reported FF30 is at byte59 in the main header, after COD and before QCD.
It is not a two-byte segment length. Main/tile header readers now skip only
FF30-FF3F, charging one work unit for each marker and preserving reader state
at work-limit or truncation failures. Delimiting/header order, unknown marker
handling, segment lengths, input bounds and entropy data are otherwise unchanged.
No compatibility flag or `PdfRecovery` is required.

## Proof correction

The previous exact reader models encoded the same incorrect interpretation
as the implementation; passing those models did not establish the A.1.3 rule.
`part1_skip_reserved_markers` now models bounded skipping, and actual
main/tile header contracts compose it with their original post-skip bodies.
The default production implementation itself is verified. No assumption,
budget increase or verification exclusion was added.

## Regression and provenance

The fixture is from the MIT-licensed Hayro repository at revision
`e7ada1354dff4041cdeed3d8ba56fe01b6186132`, path
`hayro-jpeg2000/tests/streams/codestream_reserved_marker.j2k`.
Its SHA256 is
`27877d3091232033d36cd98b62eb843f74971a8689d9a48b5f13f4fe274c7f9f`.
The accompanying license retains the upstream attribution.

The original current-main/published0.2.1 rejection is `Truncated` at byte59.
The corrected strict decoder returns128x96, one unsigned8-bit component.
All12,288 samples match independent OpenJPEG2.5.4 output exactly, sample-byte
SHA256 `b99f348fe8bd86f3bb26bad6217f37abfa5e182244dff74459b1bec27c1d8106`.
OpenJPEG is a numerical cross-check, not the normative classification source.

Native tests cover both headers, every marker in the reserved range, repeated
markers, exact work limits, truncated prefixes and adjacent unknown codes.
The full fixture regression also tests all16 codes and continued rejection of
adjacent unknown markers/truncation. Existing exhaustive header state/error
tests retain their independent reference paths with the required skip step.
