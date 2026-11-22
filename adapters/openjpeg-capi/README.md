# OpenJPEG decode compatibility adapter

Experimental source-compatible subset of OpenJPEG 2.5.4. This package is
unpublished and is not a binary or system-wide replacement for `libopenjp2`.
Build `jpeg2000-openjpeg-compat` as a Rust static library, then compile
`shim.c` against the consumer's matching `openjpeg.h` and link both into the
consumer. Do not link the adapter and OpenJPEG into the same program.

The adapter supports full-image J2K and single-codestream JP2 decoding
over synchronous read callbacks, including resolution reduction. It buffers
the declared stream length (up to 16 MiB); it does not call seek or skip
callbacks. Decoded planes use C allocations and are released with
`opj_image_data_free` or `opj_image_destroy`. Rust-owned images stay internal.
The adapter admits up to 32 million reference-grid samples across components
and sets the decoder's decoded-bytes limit to 256 MiB. The exported decoded
planes are also limited to 32 million samples in total, including palette
expansion.
Information and warning callbacks are accepted but not invoked; decoder
errors are reported through the error callback.

Non-zero image origins are preserved in the reference-grid bounds and component
offsets. Non-indexed JP2 input applies the crate's palette and component
mappings; `opj_decode` can therefore replace the component array and change
`numcomps`. The returned planes retain their individual native precision,
signedness and sampling, and expose decoded opacity/premultiplied-opacity
flags. Indexed input exposes raw codestream components when the caller sets
`OPJ_DPARAMETERS_IGNORE_PCLR_CMAP_CDEF_FLAG`.

The adapter recognizes enumerated sRGB, grayscale, sYCC and CMYK metadata.
Other color metadata, including ICC methods, is admitted as
`OPJ_CLRSPC_UNSPECIFIED` without transforming the samples or exporting an ICC
profile. Acceptance is not a claim of color-management support; consumers must
provide an appropriate color interpretation. No extra CDEF channel reordering
is performed by the adapter.

Encoding, partial areas, individual tile extraction and quality-layer selection
are not supported. Native sample export remains limited to 31-bit precision and
values representable by `int32_t`. Output uses a separate C sample allocation,
so peak memory is not expected to match the direct Rust API. Build the Rust
library and `shim.c` together; their private bridge layout is not a stable ABI.
The updated bridge symbols use a `_v2` suffix so mismatched older C/Rust
halves fail to link rather than interpreting incompatible layouts.

Strict decoding is the default. Calling `opj_decoder_set_strict_mode(codec,
OPJ_FALSE)` before reading the header opts into the crate's bounded PDF recovery
for inspection and decoding. This supports the crate's documented recoveries,
not every permissive behavior of OpenJPEG.

`probe.c` is a small standalone consumer that exercises the header, stream,
decode, and destruction sequence. Build it once against the OpenJPEG header
and link separately against OpenJPEG and the shim to compare native samples.

## Regression tests

The C regression suite generates small original codestreams and containers in
memory. It checks offset/subsampled/reduced images, palette expansion with
signed/native-precision samples and opacity, indexed input, lenient JP2 EOL
recovery, unhandled color metadata, and failure cleanup without replacing the
caller's header. On Linux with an OpenJPEG development header and `pkg-config`:

```sh
cargo build -p jpeg2000-openjpeg-compat --release --locked
cc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined \
  $(pkg-config --cflags libopenjp2) \
  adapters/openjpeg-capi/shim.c adapters/openjpeg-capi/tests/regression.c \
  target/release/libjpeg2000_openjpeg_compat.a -lpthread -ldl -lm \
  -o target/openjpeg-adapter-tests
ASAN_OPTIONS=detect_leaks=1 ./target/openjpeg-adapter-tests
cargo clippy -p jpeg2000-openjpeg-compat --all-targets --locked -- -D warnings
```

Only the header flags from `pkg-config` are used: do not link OpenJPEG's library
into the shim test executable. The decoder itself remains memory-safe Rust;
the sanitizers here instrument the C shim and test harness.
