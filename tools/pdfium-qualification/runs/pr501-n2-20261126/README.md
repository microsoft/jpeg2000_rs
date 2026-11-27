# PR501 exact-source N2 qualification (Base c7b8473 vs PR501 4e78ee6)

## Functional-only checkpoint

Actually completed sources: **Base, PR501**.
Full functional/reference phases still pending for: **none**.
Performance is **pending**; no timing/adoption claim is implied.

All completed sources have the original2,521 requests (310 images x8 plus41
genuinely lenient PDF renders), actual native build/optimization/source-pair
audits,17 Shim +6 FFI real targeted tests and ten independent controls.
The new c7b8473 Base is executed fresh, not inherited from 38bd, bd02, d727, 043b, b51a, 7790, f4b, 54ab, or a99.

Source map requested by #490 comment 7206727101:

- Base: `c7b8473e7aedddba23989753679627c361a3a34a`
- PR501: `4e78ee66b6a3541ae9e875d1eb8dca00a70813e4`

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
