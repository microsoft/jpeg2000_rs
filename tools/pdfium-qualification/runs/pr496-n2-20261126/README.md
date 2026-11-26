# PR496 exact-source N2 qualification (Base 7790a4e vs PR496 b51a413)

## Functional-only checkpoint

Actually completed sources: **Base, PR496**.
Full functional/reference phases still pending for: **none**.
Performance is **pending**; no timing/adoption claim is implied.

All completed sources have the original2,521 requests (310 images x8 plus41
genuinely lenient PDF renders), actual native build/optimization/source-pair
audits,17 Shim +6 FFI real targeted tests and ten independent controls.
The new 7790a4e Base is executed fresh, not inherited from f4b, 54ab, or a99.

Source map requested by #490 comment 7195089004:

- Base: `7790a4ee1237f6af7253109bf797f1d1e669bf5e`
- PR496: `b51a41301aa83b6d71d902ca0dbb6c0dcea628c0`

Original immutable harness:90dd9f013c35739a7d67de869180b62a08bcea23.
Native Neoverse-N2, exact original matching LLVM24, O3/native/CGU1/ThinLTO/
final-linkO3, default features and2GiB data cap are retained. Within every
completed source, C/Rust shim halves match and Shim/FFI core archives are
identical. The original OpenJPEG binary is unchanged.

Actual command hashes and location-only projections are supplied; source
labels retain exact identity while temporary paths are removed. Original XML
outcomes and every status/pixel/refusal remain. The 46-test aggregate records
both sources' completed native tests; receipt per-source test counts only
the completed functional/reference sources in this checkpoint.

No decoder, corpus, arithmetic, limits, policy, release/backport, owner
tradeoff, merge or adoption was changed. Later combined adoption needs a
separate exact-tree qualification. Historical receipts and negative evidence
are not relabeled or erased.
