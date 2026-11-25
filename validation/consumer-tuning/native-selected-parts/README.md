# Selected tile-part qualification fixtures

These files are first-party synthetic JPEG 2000 codestreams under the
repository's [MIT license](../../../LICENSE). They reproduce the exact #481
fixed-pixel attribution inputs, not any external integration corpus.

Both files contain 1,027 bytes: a 32×1 image at origin zero, 32 one-pixel
tiles, two parts per tile, and one empty packet per part. `grouped.j2k`
orders `(tile, ordinal)` as `(0,0), (0,1), (1,0), (1,1), …`;
`interleaved.j2k` emits all ordinal-0 parts and then all ordinal-1 parts.
All samples must be 128 (unsigned 8-bit), with unit subsampling, zero
registration, and empty CDEF. The ROI at `(31,0,1,1)` retains just the last
pixel at origin `(31,0)`.

| File | SHA-256 |
| --- | --- |
| `grouped.j2k` | `5e73c697e14e9d669ef58c2438a70cd55b1cba8c888633374bb7e47b656a0eef` |
| `interleaved.j2k` | `eeae0a6f3927776a2446cca9293d0f58d719e4efff50c2f96ed81e6b84f8c5df` |

The probe differs from the original local probe (`6a8d974209aca3dbdeb6c7a4a29a7f94afb95a05ac1d97b18f45b7f4badb0227`)
only by explicitly binding `std::alloc::System`; native probe SHA-256 is
`d8646e85db9c851ac093f3bd097aa92a70b25606ccdc2e1b641db16d6c2002be`.
There is no allocator pooling or instrumentation.

The selected-parts helper also explicitly admits the ordered
`f4b2b7b29d38fa31bd74263913462bb67d6e5e4e` /
`2743436c341a679ce62162f3fc3ef72807b98dee` pair, with the original defaults
and earlier approved pairs unchanged. This remains the **32×1/512-call**
cohort. The separate [seeded32 scaling helper](../native-index-scaling/README.md)
qualifies the actual fixed-pixel COPY-index target using all 13 paths and
its distinct six-call protocol; neither replaces the original consumer gates.
