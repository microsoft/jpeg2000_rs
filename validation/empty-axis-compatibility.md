# Empty intermediate wavelet axes (#423, #424)

## Normative classification

Both reports exercise valid Part1 geometry, not recoverable malformed syntax.
ITU-T T.800 (06/2019) / ISO/IEC15444-1:2019 A.5.1 defines reference-grid/tile
bounds, B.5 defines reduced-resolution/subband coordinate bounds, and F.3.2-F.3.6
reconstruct the corresponding domains. A reduced subband can be empty even
though the final image and clipped tile are nonempty. F.3.6 separately defines
the odd-origin single-sample high-pass division by two.

The #423 grid satisfies its tile-origin constraints, but its first clipped
tile is only3 samples wide with5 decomposition levels. Some intermediate
resolution widths are zero. The #424 row at y=45 has empty low-pass rows at
intermediate levels; its final high-only singleton axis is legitimate.

The acquired T.800(06/2019) reference SHA256 is
`9932e967462cd56a193db87117917e74734fb385913bf51d1f52fb0428924e1c`.
The selected2024 full text was not acquired and is not claimed reconciled.
Reference decoder acceptance is not the conformance argument.

## Root cause and proof correction

Decoder preparation routed empty intermediate domains through the standalone
nonempty inverse-level API, whose exact model correctly described that API's
`InvalidTransform` policy but not the necessary internal domain.

A separate private empty-level operation validates all four band dimensions,
parities and exact sample lengths and retains arithmetic/byte-budget checks.
Only then does it return the empty plane in constant time without allocation
or scanning the other, potentially large, axis. Nonempty reconstruction and
standalone zero-shape rejection are unchanged. Whole-image SIZ/resource limits
and singleton lifting/rounding are unchanged.

The actual empty operation and decoder request/fold model are updated and
verified; no success premise, assumption, budget increase or verification
exclusion is added. No non-strict mode or recovery report is needed.

## Exact original inputs and results

The three MIT-licensed fixtures are from Hayro revision
`e7ada1354dff4041cdeed3d8ba56fe01b6186132`, under
`hayro-jpeg2000/tests/streams/`, with retained upstream license:

| Fixture | SHA256 |
|---|---|
| codestream_offset_large.j2k | 2336b98e18cc29fa24f3c5d659cc1d29bbf37532d0face8124fa787694e3257e |
| quantization_irreversible_offset_large.j2k | 53536c64031910a4dffb49b572d9f7a21c3a5e79b8d1f61bcdfad002e648087f |
| codestream_single_row_odd_offset.j2k | 1b9e36c1e8b82f627fc801fc0146fb8a6304121a7e75f235a8fdc97f4635749f |

Strict full and full-selection decoding now succeed with correct dimensions
and origins:128x96 at(3097,41), and128x1 at(0,45).
All12,288 reversible large-origin and128 singleton samples match independent
OpenJPEG2.5.4 exactly. The irreversible fixture retains the decoder's existing
numerical convention:117 of12,288 samples differ from OpenJPEG by at most1.
This is disclosed, not called exact parity or hidden by a new tolerance.
The regression locks the unchanged checked-arithmetic model's native output.

Native tests cover both empty axes, all parity combinations, enormous other
axis with no scanning/allocation, malformed band dimensions/sample lengths,
and unchanged public zero-shape rejection. Exact fixture tests cover strict
full/selected samples, metadata and source origins.
