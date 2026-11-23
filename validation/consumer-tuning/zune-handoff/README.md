# Actual zune consumer handoff

These files come from [issue #449's consumer handoff](https://github.com/microsoft/jpeg2000_rs/issues/449#issuecomment-7071726628).
They are separate from the standalone consumer study.

The public zune source is pinned to `fa80e24b17ff388ac850d6042bdca391f9913c4e`.
The independent harness lock resolves published decoder 0.2.2 and Hayro 0.3.5.
The patch's terminal blank line was restored so its final Git binary fixture
applies completely; the two fixture Git blob IDs remain exactly those supplied.
No adapter algorithm was changed. For adapter unit tests only, the zune workspace
lock is rolled from 0.2.1 to 0.2.2, and `jpeg` is enabled because an unrelated
upstream colorspace test unconditionally imports that optional dependency.
The measured harness enables only the supplied JPEG 2000 features.

Generate once with Python 3.12, Pillow 12.0.0 and OpenJPEG 2.5.4, then verify
all sixteen entries in `SHA256SUMS`. Native runners must consume the same
verified eight JP2 inputs and references, not different re-encodings.

```sh
python3 ../zune_integration.py prepare --work-root /new/scratch/consumer
python3 ../zune_integration.py run --work-root /new/scratch/consumer \
  --fixtures /verified/historical/fixtures --output /new/results --pairs 4
```

The driver reuses the existing measured compiler/linker wrappers and process
RSS collector. Every profile is built twice from fresh targets in opposite
order. Each backend is compared to its own generic bytes; changed outputs
disqualify that backend's timing. Lossy reference differences remain visible.
The explicit tuning CPU comes from the pinned compiler's actual native CPU
detection, and both executable and decoder compilation flags are checked.
Generic flags remain portable defaults. Build/link/text size, process memory,
per-fixture median/p90 and matched-process-block uncertainty are separate.

This does not qualify PDFium: GN configuration and direct backend integration
must be measured independently. Full raw evidence belongs outside tracked
source and no private PDF inputs are uploaded.

The supplied example Hayro corpus revision did not resolve through the public
commit API or Git. Broader strict/lenient artifact acceptance therefore uses a
separately labeled fixed public corpus from published source anchor
`4989f9c680beeb7bad4fbfd441a93aa373d2ba4f`, not an unpinned HEAD.
`zune_acceptance.py` records each input, status and output against its backend's
own generic result. Each file runs in its own bounded process so a malformed
input cannot hide later cases; process failures and timeouts remain explicit.
CPU-specific artifacts are not executed on a mismatched native CPU.
