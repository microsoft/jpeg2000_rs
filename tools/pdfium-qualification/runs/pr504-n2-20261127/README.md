# PR504 exact-source N2 qualification (Base ec5d3f0 vs PR504 8c82b53)

## Functional-only checkpoint

Actually completed sources: **Base, PR504**.
Full functional/reference phases still pending for: **none**.
Performance is **pending**; no timing/adoption claim is implied.

All completed sources have the original2,521 requests (310 images x8 plus41
genuinely lenient PDF renders), actual native build/optimization/source-pair
audits,17 Shim +6 FFI real targeted tests and ten independent controls.
The new ec5d3f0 Base is executed fresh, not inherited from fe0d, c7b8, 38bd, bd02, d727, 043b, b51a, 7790, f4b, 54ab, or a99.

Source map requested by #490 comment 7225882509:

- Base: `abea3a339689afdf39f37244de9d0f1ecfe10a69`
- PR504: `f72f5dd94527d70e5e8a168750c1f871c8788727`

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
