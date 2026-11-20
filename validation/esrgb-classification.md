# Issue #439: PIMA e-sRGB and explicit OpenJPEG compatibility

The former PIMA-definition blocker is resolved by the user's supplied standard.
Two deliberately separate paths are implemented: the actual PIMA conversion
for supported conforming sample encodings, and an explicit, reported RGB
interpretation for the original nonconforming eight-bit declaration.

## Normative basis and original input

* Acquired T.800 (06/2019), I.5.3.3/Table I.10, limits core JP2 enumerated
  colors to 16, 17 and 18. Its PDF SHA-256 is
  `9932e967462cd56a193db87117917e74734fb385913bf51d1f52fb0428924e1c`.
* Acquired T.801 (06/2021), M.11.7.3.1/Table M.25, registers JPX EnumCS20
  by reference to PIMA 7667. M.9.2.4 includes e-sRGB in JPX baseline color
  methods. Its PDF SHA-256 is
  `8ec28b54b53f5b6898a02d0718566600809e1c86ecbbf64ab0e1e443e7f67f40`.
* The [user-supplied PIMA 7667:2001 copy](https://www.13thmonkey.org/documentation/fonts/pima7667-2001.pdf)
  identifies the first edition approved 2001-05-18. Its SHA-256 is
  `05653ec7b3b42ad3d8b1a023dc21cfb7af69a7b8ba30c88003d20c46c40d9c20`.
  Section 4.1 defines 10-, 12- and 16-bit encoding, not eight-bit encoding.
  Normative Annex A supplies the direct coded-sRGB embedding and default
  RGB-clipped inverse. The supplied copy is not represented as a
  publisher-authenticated binary.

No PDF or extracted standards text is redistributed. The selected newer ITU
editions in [REFERENCES.md](../REFERENCES.md) remain unreconciled; this work
does not claim complete standards conformance.

The original [fixture](fixtures/hayro-esrgb/jp2_colr_esrgb.jp2) is unchanged:
128 by 96, three unsigned eight-bit unit-sampled channels, no palette/CDEF,
JP2-only brand and compatibility list, and first/only EnumCS20. Its SHA-256 is
`1dccce55ca6427f9a9eaa47cdd0d2cf953ea331822a604f60b5c606aefd36af9`.
It comes from
[LaurenzV/hayro@e7ada1354dff4041cdeed3d8ba56fe01b6186132](https://github.com/LaurenzV/hayro/tree/e7ada1354dff4041cdeed3d8ba56fe01b6186132),
`hayro-jpeg2000/tests/streams/jp2_colr_esrgb.jp2`, with the adjacent unchanged
[upstream MIT license](fixtures/hayro-esrgb/LICENSE-MIT).
Its branding and precision are independently nonconforming. Native plane
acceptance does not validate its color declaration.

## PIMA conversion

For precision `n` in `{10,12,16}`, the encoded-sRGB offset is
`3 * 2^(n-3)` and the step is `2^(n-9)`. Black/white codes are:

| Precision | Black | White | Step |
|---|---:|---:|---:|
| 10 | 384 | 894 | 2 |
| 12 | 1536 | 3576 | 8 |
| 16 | 24576 | 57216 | 128 |

The converter computes
`round_half_up(clamp((sample - offset) / step, 0, 255) * 257)`.
Clipping is in encoded RGB, not XYZ. No floating-point gamma round trip is
necessary for this direct coded-RGB conversion. Sixteen-bit half-up
quantization is our output policy, not a PIMA-mandated rounding rule.
All 256 embedded eight-bit sRGB codes return exactly `code * 257`.
Extended values are preserved in native images and clipped only when
requesting converted sRGB output; fitting the bits alone does not establish
physical colorimetric validity of every possible triplet.

The full converter checks three unsigned components of a uniform supported
precision, follows existing CDEF color ordering and nominal grid sampling/
registration, and retains resource checks and fallible output owners.
Alpha associations are explicitly unsupported, not guessed or unpremultiplied.
Existing grayscale/sRGB/sYCC/ICC policies and the public output-space enum
are unchanged.

Strict JP2 color entry points check the extended color declaration against
recognized JPX compatibility at the display-profile stage, before entropy
decoding. This intentional new metadata check does not tighten native-plane
entry points. JPX-only carriers use the existing JPX color APIs. Changing only
branding cannot make an eight-bit encoding valid; changing only precision
cannot justify a JP2-only e-sRGB declaration.

## Explicit compatibility path

Measured OpenJPEG 2.4.0/2.5.4 behavior accepts the original fixture and writes
the three decoded planes unchanged as RGB. The 2.5.4 core reports
`UNKNOWN(-1)` for EnumCS20 versus `SRGB(1)` for the EnumCS16-only control;
it has no e-sRGB-specific conversion. Hayro 0.3.5/0.5.0 scalar core also
produces the same RGB bytes with both values of its strict flag.
All seven tested engine/mode paths on both original/control inputs agree on
all 36,864 byte samples, SHA-256
`732e19ab48d019f8f65f2ae97f069bd554cc49d9123f5516f8a41786b54af014`.
This is an interoperability reference, not a PIMA colorimetric oracle.

The additive `convert_jp2_color_compatible` and
`decode_jp2_color_compatible` return `CompatibleColorImage` containing:

* `image`: the existing sixteen-bit `ConvertedImage`;
* `recovery.assumed_srgb_for_8bit_esrgb`: true only when the explicit
  full-resolution, unregistered, three-plane unsigned eight-bit EnumCS20
  interpretation was used.

That path uses ordinary RGB normalization, so the original eight-bit samples
become `sample * 257`, reversibly matching the measured OpenJPEG bytes.
Other inputs use strict conversion. There is no global hidden fallback,
changed `DecodeOptions`, new output enum variant, fallback decoder, or claim
that eight-bit e-sRGB is defined by PIMA. Existing strict full and selected
APIs still reject the original fixture.

The convenience decode call reuses native JP2 decoding, reparses container
metadata, then invokes the compatible converter. Both actual parser passes
and their fallible allocations/errors occur in its source-derived cold model.
Limits retain their stage-local meanings rather than becoming an undocumented
cumulative budget.

## Independent regressions and proof boundary

[The Python regressions](tests/test_esrgb_classification.py) exercise actual
native, full/selected strict, and explicit compatible public callers:

* the exact original native image and strict errors remain;
* the complete compatible RGB result matches the measured OpenJPEG hash,
  reports its assumption, preserves refusals and leaves ordinary sRGB unflagged;
* 10/12/16-bit JPX images contain all embedded sRGB bytes plus extended,
  clipping, fractional and half-way codes, tested in full and selected output;
* expected converted values use independent rational arithmetic and PIMA's
  black/white anchors, not the implementation/model or OpenJPEG color conversion;
* independent branding/precision controls remain rejected.

[The generator](generate_esrgb_fixtures.py) reproduces the self-authored
137-by-2 RGB fixtures using OpenJPEG 2.4.0 lossless encoding, one resolution
and no MCT. It constructs JPX-only, minor-version-1 carriers; no standards
image is copied. The fixtures inherit the repository license and are excluded
from the Rust package, as is the original validation fixture.

| Fixture | SHA-256 |
|---|---|
| `pima-10.jpx` | `2ae38a181760778c733498bff4e13363ddab03b4de124f7285ac3b0503daecaf` |
| `pima-12.jpx` | `44285381f5f077010e8e62e3ebb23daa796629c0cc186c919f98910371b0e8f4` |
| `pima-16.jpx` | `12dfb53dc930c0fbd927208cc56fe1681cf49d8ae58bfdf7cf0f0e2fb3ebede1` |

Native tests additionally cover source shape/sign/precision, CDEF, alpha
rejection, origins/subsampling/registration, exact first sample failure,
every reached storage refusal and retry, and unchanged existing color paths.
Verus binds actual scalar/image/dispatch implementations and public callers
to the source-derived results, ordered storage and recovery report, with a
universal embedded-byte roundtrip theorem. These are implementation-to-model
guarantees, not independent normative-model completeness proofs. Independent
equations/vectors and classification are needed precisely because refinement
alone cannot discover a shared specification/model omission.

The maintained inventory links these contracts/models/proofs/tests; it is not
an exhaustive clause-coverage metric. Qualification retains the existing
pinned verifier, full source and actual packaged-archive gates, source binding,
five Rust-only adapters, lifetime-disabled profile boundary, and
source-function coverage reported as `not-measured`. No assumptions,
verification exclusions, proof budgets, numerical tolerances or trust
boundaries are changed.
