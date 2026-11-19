# OpenJPEG decode compatibility adapter

Experimental source-compatible subset of OpenJPEG 2.5.4. This package is
unpublished and is not a binary or system-wide replacement for `libopenjp2`.
Build `jpeg2000-openjpeg-compat` as a Rust static library, then compile
`shim.c` against the consumer's matching `openjpeg.h` and link both into the
consumer. Do not link the adapter and OpenJPEG into the same program.

The adapter supports strict, full-image J2K and single-codestream JP2 decoding
over synchronous read callbacks, including resolution reduction. It buffers
the declared stream length (up to 16 MiB); it does not call seek or skip
callbacks. Decoded planes use C allocations and are released with
`opj_image_data_free` or `opj_image_destroy`. Rust-owned images stay internal.
Information and warning callbacks are accepted but not invoked; decoder
errors are reported through the error callback.

Encoding, partial areas, individual tile extraction, quality-layer selection,
ICC profiles, non-zero image origins, and non-strict recovery are not
supported. Indexed input can expose raw codestream components when the caller
sets `OPJ_DPARAMETERS_IGNORE_PCLR_CMAP_CDEF_FLAG`; general palette expansion is
not supported. Output uses a separate C sample allocation, so peak memory is
not expected to match the direct Rust API.

`probe.c` is a small standalone consumer that exercises the header, stream,
decode, and destruction sequence. Build it once against the OpenJPEG header
and link separately against OpenJPEG and the shim to compare native samples.
