# PR492 / PR493 / PR494 exact-source N2 qualification

## Functional-only checkpoint

Actually completed sources: **Base**.
Full functional/reference phases still pending for: **PR492, PR493, PR494**.
Performance is **pending**; no timing/adoption claim is implied.

All completed sources have the original2,521 requests (310 images x8 plus41
genuinely lenient PDF renders), actual native build/optimization/source-pair
audits,17 Shim +6 FFI real targeted tests and ten independent controls.
The new f4b Base is executed, not inherited from54ab or a99.

Source map requested by #490 comment7177635722:

- Base: `f4b2b7b29d38fa31bd74263913462bb67d6e5e4e`
- PR492: `557960d2e36526d82fd0971c3dc5463219880c7b`
- PR493: `590ca79a111f701308665038a83915434d551e80`
- PR494: `2743436c341a679ce62162f3fc3ef72807b98dee`

Original immutable harness:90dd9f013c35739a7d67de869180b62a08bcea23.
Native Neoverse-N2, exact original matching LLVM24, O3/native/CGU1/ThinLTO/
final-linkO3, default features and2GiB data cap are retained. Within every
completed source, C/Rust shim halves match and Shim/FFI core archives are
identical. The original OpenJPEG binary is unchanged.

Actual command hashes and location-only projections are supplied; source
labels retain exact identity while temporary paths are removed. Original XML
outcomes and every status/pixel/refusal remain. The92-test aggregate records
all four sources' completed native tests; receipt per-source test counts only
the completed functional/reference sources in this checkpoint.

No decoder, corpus, arithmetic, limits, policy, release/backport, owner
tradeoff, merge or adoption was changed. Later combined adoption needs a
separate exact-tree qualification. Historical receipts and negative evidence
are not relabeled or erased.
